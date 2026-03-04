import subprocess
import os
import csv
import concurrent.futures
from collections import defaultdict

import tree_sitter_cpp
from tree_sitter import Language, Parser, Query, QueryCursor

# ==========================================
# 1. Global Tree-sitter Initialization
# ==========================================
CPP_LANGUAGE = Language(tree_sitter_cpp.language())
parser = Parser(CPP_LANGUAGE)

QUERY_STRING = """
(field_declaration
  type: [
    (template_type) @tmpl
    (qualified_identifier (template_type) @tmpl)
  ]
) @field
"""
query = Query(CPP_LANGUAGE, QUERY_STRING)

# ==========================================
# 2. Helper Functions
# ==========================================

def get_git_files():
    """Run git ls-files and return C/C++ file paths, filtering third_party, ios, and tools."""
    print("Running git ls-files to discover source files...")
    try:
        result = subprocess.run(
            ['git', 'ls-files'], 
            capture_output=True, 
            text=True, 
            check=True
        )
        files = result.stdout.splitlines()
        
        cpp_files = []
        for f in files:
            if not f.endswith(('.h', '.hpp', '.cc', '.cpp')):
                continue
            if 'ios' in f:
                continue
            if f.startswith('tools/'):
                continue
            if f.startswith('third_party/') and not f.startswith('third_party/blink/'):
                continue
                
            cpp_files.append(f)
            
        return cpp_files
    except subprocess.CalledProcessError as e:
        print(f"Error running git ls-files: {e}")
        return []

def get_container_name(tmpl_node):
    name_node = tmpl_node.child_by_field_name('name')
    if not name_node:
        return None
        
    if name_node.type == 'scoped_type_identifier':
        final_name_node = name_node.child_by_field_name('name')
        if final_name_node:
            text = final_name_node.text.decode('utf8')
        else:
            text = name_node.text.decode('utf8').split('::')[-1]
    else:
        text = name_node.text.decode('utf8')
    
    return text.split('<')[0].strip()

def is_raw_ptr_or_ref(node):
    text = node.text.decode('utf8').replace(' ', '').replace('\n', '')
    if text.startswith('raw_ptr<') or text.startswith('base::raw_ptr<') or \
       text.startswith('raw_ref<') or text.startswith('base::raw_ref<'):
        return True

    if node.type == 'template_type':
        name = get_container_name(node)
        if name in ('raw_ptr', 'base::raw_ptr', 'raw_ref', 'base::raw_ref'):
            return True
        return False

    for child in node.children:
        if is_raw_ptr_or_ref(child):
            return True
    return False

def contains_function_declarator(node):
    if node.type in ('function_declarator', 'abstract_function_declarator'):
        return True
    for child in node.children:
        if contains_function_declarator(child):
            return True
    return False

def is_inside_function_declarator(node, root):
    curr = node.parent
    while curr is not None:
        if curr.type in ('function_declarator', 'abstract_function_declarator'):
            return True
        if curr == root:
            break
        curr = curr.parent
    return False

def is_raw_pointer_type(node, root=None):
    if root is None:
        root = node
        
    if node.type in ('pointer_declarator', 'abstract_pointer_declarator'):
        if not contains_function_declarator(node) and not is_inside_function_declarator(node, root):
            return True
            
    if node.type == 'template_type':
        return False

    for child in node.children:
        if is_raw_pointer_type(child, root):
            return True
    return False

def is_method_declaration(field_node):
    type_node = field_node.child_by_field_name('type')
    for child in field_node.children:
        if child == type_node:
            continue
        if contains_function_declarator(child):
            return True
    return False

def is_ignored_ptr_type(node):
    """Checks if the node represents a const char* or const char* const type, including inside raw_ptr."""
    text = node.text.decode('utf8').replace(' ', '').replace('\n', '')
    
    # Strip raw_ptr / raw_ref wrappers to check the inner type
    for prefix in ('raw_ptr<', 'base::raw_ptr<', 'raw_ref<', 'base::raw_ref<'):
        if text.startswith(prefix) and text.endswith('>'):
            text = text[len(prefix):-1]
            break
            
    return text in (
        'constchar*',
        'charconst*',
        'constchar*const',
        'charconst*const'
    )

def get_access_level(field_node):
    """Walks tree siblings backward to determine if field is public/private/protected."""
    parent = field_node.parent
    if not parent or parent.type != 'field_declaration_list':
        return 'unknown'
    
    grandparent = parent.parent
    current_access = 'private'
    if grandparent:
        if grandparent.type in ('struct_specifier', 'union_specifier'):
            current_access = 'public'
        elif grandparent.type == 'class_specifier':
            current_access = 'private'
    
    for child in parent.children:
        if child == field_node:
            break
        if child.type == 'access_specifier':
            text = child.text.decode('utf8').replace(':', '').strip()
            if text in ('public', 'private', 'protected'):
                current_access = text
                
    return current_access

def get_default_counts():
    return {'raw_ptr_or_ref': 0, 'raw_pointer': 0}

# ==========================================
# 3. Worker Function (Runs in parallel)
# ==========================================

def process_file(file_path):
    local_test = defaultdict(get_default_counts)
    local_prod = defaultdict(get_default_counts)
    local_instances = []

    if not os.path.isfile(file_path):
        return local_prod, local_test, local_instances
        
    is_test_file = 'test' in os.path.basename(file_path).lower()
    target_counts = local_test if is_test_file else local_prod

    try:
        with open(file_path, 'rb') as f:
            source_code = f.read()
            
        tree = parser.parse(source_code)
        cursor = QueryCursor(query)
        matches = cursor.matches(tree.root_node)
        
        for match in matches:
            captures = match[1]
            
            field_nodes = captures.get('field', [])
            tmpl_nodes = captures.get('tmpl', [])
            
            if not field_nodes or not tmpl_nodes:
                continue
                
            # Grab the specific nodes matched in this capture tuple
            field_node = field_nodes[0] if isinstance(field_nodes, list) else field_nodes
            tmpl_node = tmpl_nodes[0] if isinstance(tmpl_nodes, list) else tmpl_nodes
            
            if is_method_declaration(field_node):
                continue
            
            args_node = tmpl_node.child_by_field_name('arguments')
            if not args_node or args_node.type != 'template_argument_list':
                continue
                
            container_name = get_container_name(tmpl_node)
            if not container_name:
                continue
                
            found_raw_ptr_or_ref = False
            found_raw_pointer = False
            
            for child in args_node.children:
                if not child.is_named:
                    continue
                    
                if is_ignored_ptr_type(child):
                    continue
                    
                if is_raw_ptr_or_ref(child):
                    found_raw_ptr_or_ref = True
                elif is_raw_pointer_type(child):
                    found_raw_pointer = True
            
            if found_raw_ptr_or_ref or found_raw_pointer:
                # 1. Update aggregates
                if found_raw_ptr_or_ref:
                    target_counts[container_name]['raw_ptr_or_ref'] += 1
                if found_raw_pointer:
                    target_counts[container_name]['raw_pointer'] += 1
                
                # 2. Record this specific instance
                access_level = get_access_level(field_node)
                type_node = field_node.child_by_field_name('type')
                full_type = ' '.join(type_node.text.decode('utf8').split()) if type_node else ''
                
                local_instances.append({
                    'file_path': file_path,
                    'is_test': 'TRUE' if is_test_file else 'FALSE',
                    'container_type': container_name,
                    'protected_by_raw_ptr': 1 if found_raw_ptr_or_ref else 0,
                    'protected_modifier': 1 if access_level == 'protected' else 0,
                    'access_level': access_level,
                    'line_number': field_node.start_point[0] + 1,
                    'full_type': full_type
                })

    except Exception:
        pass

    return local_prod, local_test, local_instances

# ==========================================
# 4. Main Execution & Aggregation
# ==========================================

def write_counts_csv(filename, counts_prod, counts_test):
    print(f"Writing summary results to {filename}...")
    with open(filename, 'w', newline='', encoding='utf8') as f:
        writer = csv.writer(f)
        writer.writerow([
            'Member Type', 
            'Production raw_ptr<T>', 'Production T*', 'Production Total',
            'Test raw_ptr<T>', 'Test T*', 'Test Total',
            'Grand Total'
        ])
        
        all_containers = sorted(set(counts_prod.keys()) | set(counts_test.keys()))
        
        for container in all_containers:
            prod = counts_prod.get(container, {'raw_ptr_or_ref': 0, 'raw_pointer': 0})
            test = counts_test.get(container, {'raw_ptr_or_ref': 0, 'raw_pointer': 0})
            
            prod_total = prod['raw_ptr_or_ref'] + prod['raw_pointer']
            test_total = test['raw_ptr_or_ref'] + test['raw_pointer']
            grand_total = prod_total + test_total
            
            if grand_total > 0:
                writer.writerow([
                    container,
                    prod['raw_ptr_or_ref'], prod['raw_pointer'], prod_total,
                    test['raw_ptr_or_ref'], test['raw_pointer'], test_total,
                    grand_total
                ])

def main():
    cpp_files = get_git_files()
    total_files = len(cpp_files)
    print(f"Found {total_files} C/C++ files to scan. Running in parallel...\n")

    global_counts_test = defaultdict(get_default_counts)
    global_counts_prod = defaultdict(get_default_counts)

    # Open the instances CSV to stream output immediately (saves memory)
    instances_csv_path = 'template_member_instances.csv'
    print(f"Opening {instances_csv_path} for streaming output...")
    instances_file = open(instances_csv_path, 'w', newline='', encoding='utf8')
    instances_writer = csv.writer(instances_file)
    instances_writer.writerow([
        'File Path', 'Is Test File', 'Container Type', 
        'Protected by raw_ptr (0/1)', 'Protected Modifier (0/1)', 
        'C++ Access Level', 'Line Number', 'Full Type'
    ])

    # Use a ProcessPoolExecutor to max out CPU cores
    with concurrent.futures.ProcessPoolExecutor() as executor:
        results = executor.map(process_file, cpp_files, chunksize=50)

        for index, (local_prod, local_test, local_instances) in enumerate(results):
            if (index + 1) % 5000 == 0:
                print(f"Processed {index + 1} / {total_files} files...")

            # Aggregate production counts
            for container, counts in local_prod.items():
                global_counts_prod[container]['raw_ptr_or_ref'] += counts['raw_ptr_or_ref']
                global_counts_prod[container]['raw_pointer'] += counts['raw_pointer']

            # Aggregate test counts
            for container, counts in local_test.items():
                global_counts_test[container]['raw_ptr_or_ref'] += counts['raw_ptr_or_ref']
                global_counts_test[container]['raw_pointer'] += counts['raw_pointer']

            # Write individual instances sequentially
            for inst in local_instances:
                instances_writer.writerow([
                    inst['file_path'], inst['is_test'], inst['container_type'],
                    inst['protected_by_raw_ptr'], inst['protected_modifier'],
                    inst['access_level'], inst['line_number'], inst['full_type']
                ])

    instances_file.close()
    write_counts_csv('template_member_counts.csv', global_counts_prod, global_counts_test)
    print("Done! Check both template_member_counts.csv and template_member_instances.csv.")

if __name__ == "__main__":
    main()
