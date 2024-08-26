'''
This addon is provided under GNU General Public License
Build as of 8/26/24
'''
bl_info = {
    "name": "Motion Trail 3D",
    "author": "Wayde Brandon Moss",
    "version": (1, 2,26,20),
    "blender": (2, 80, 0),
    "location": "(PoseMode) View3D > UI Panel > Tool > Motion Trail 3D",
    "description": "Provides 3DView editable motion trails for animating bones and objects",
    "category": "Animation",
    }


import functools
import datetime 
import bpy
import gpu
from gpu_extras.batch import batch_for_shader
import mathutils
import math
from mathutils import Vector, Matrix, Quaternion,Euler
from bpy.props import (StringProperty,
                       BoolProperty,
                       IntProperty,
                       FloatProperty,
                       EnumProperty,
                       PointerProperty,
                       CollectionProperty,
                       FloatVectorProperty
                       )
from bpy.types import (Panel,
                       Operator,
                       PropertyGroup,
                       )

from bpy.types import  AddonPreferences
from bpy.app import handlers
from bpy.types import ChildOfConstraint, CopyLocationConstraint,CopyRotationConstraint,CopyScaleConstraint,CopyTransformsConstraint,KinematicConstraint,StretchToConstraint,TrackToConstraint,DampedTrackConstraint,LockedTrackConstraint


import bgl
import blf
import bpy_extras
from bpy_extras import view3d_utils
dns = bpy.app.driver_namespace
from bpy.app.handlers import persistent
import time

'''BEGIN Utility functions''' 
#region
TAG_root_action_group = '__gen_motiontrail3d__'
debug_general=False
debug_crash_search=False
debug_print_undo = False 
debug_enable_print_func_tags = False
unregistered = False 

debug_print_to_file = False
debug_print_to_file_initialized = False
debug_print_to_file_path = 'S:\\tmp\\debug_motion_trail.txt'

TAG_triplet_index = 'triplet_index'
'''0: left, 1:co, 2:right'''
TAG_control_type = 'control_type' 
'''1: value, 2: time, 3: both (for rot controls)'''
TAG_value_type = 'value_type'
BIT_value_type_value = 1
BIT_value_type_time = 2

crash_stop_everything=False
crash_tabs_count = 0
num_parents_to_show = 2
crash_call_stack = [] 
def wrap(method_name,func):
    def wrapped_func(*args, **kwargs):
        global crash_tabs_count 
        global crash_call_stack 

        parent_calls = ''
        for i in range(0,min(num_parents_to_show,len(crash_call_stack))):
            parent_calls += crash_call_stack[-1 * (i+ 1)] + ', '

        print_time('{1}starting: [{0}]... {2}'.format(method_name,'>' * crash_tabs_count, parent_calls))
        crash_tabs_count += 1


        crash_call_stack.append(method_name) 
        result = func(*args,**kwargs)
        crash_call_stack.pop()
        
        crash_tabs_count -= 1
        print_time('{1}...end: [{0}] : {2}'.format(method_name,'>' * crash_tabs_count,parent_calls))

        return result 

    return wrapped_func
    
#mainly used when a bug leads to a Blender crash and I need to find which function contains the crash
def debug_wrap_func_exec(obj,excluded_functions):
    
 
    object_methods = [method_name for method_name in dir(obj) if method_name not in excluded_functions and callable(getattr(obj, method_name)) and not method_name.startswith('__')]
    for method_name in object_methods:
        method = getattr(obj, method_name)
        #print('method: ' + method_name)

        wrapped_method = wrap(method_name,method)
        setattr(obj,method_name,wrapped_method)

nonserialized_undo_tracker={}
#on invoke(), every trail will add their draw callback to this list so that when dependencies exist, they will be called in order of parent to children
#this is so that when both trail controls are xformed, the parent will be updated and written first, then the child, resulting in the child writing the correct local values.
trail_callbacks = {}#target_name:callbackfunc
#update: the draw callback is what handles the ctrl writing, so as long as the dependency writes after the parent, it should be fine. So store draw callback, not scene update callbacks
#instead of all trails being added to Blender's scene update post list, we only create one
#which will instead add one, the root callback which calls the trail calllbacks
#reason: to have simpler control over the update order of trails, only necessary when trails depend on eachother.
#use: at any time, number of trails is generally at most a handful, so no need to optimize in terms of trail counts.
ordered_trail_callbacks = []
ordered_trail_nodes = [] 

#active_trails
class TrailNode():
    def __init__(self,target_name):
        self.children = []
        self.target_name = target_name 
    

def reorder_trail_updates():
    if unregistered:
        return 
        
    print_conditional(debug_enable_print_func_tags,'start of trail reordering...')
    settings = bpy.context.scene.motion_trail3D_settings
    #so need data that contains trail trailOp:[target_name, dependency name], and callback func.
    #store callbacks in dict, [target_name,callback]
    valid_active_trails = {trailOp.target_name for trailOp in settings.active_trails}
    trail_lookup = {trailOp.target_name : TrailNode(trailOp.target_name) for trailOp in settings.active_trails}
    #starts of with all items
    roots = [trailOp for trailOp in settings.active_trails]
    for i in reversed(range(0,len(roots))):
        #print_time(str(i))
        item_trailOp = roots[i]
        item_node = trail_lookup[item_trailOp.target_name]
        #print_time('looking at: ' + item_trailOp.target_name)
        if item_trailOp.dependency.is_active and (item_trailOp.dependency.target_name in valid_active_trails):
            parent = trail_lookup[item_trailOp.dependency.target_name] 
            
            parent.children.append(item_node) 
            #in the end, roots will be consistent with its definition
            del roots[i]
            #print_time('order dep. detected: {0} depends on {1}'.format(item_node.target_name,parent.target_name))
    
    
    if settings.enable_relative_parent:
        valid_dependency_targets = {trail.target_name:trail for trail in settings.active_trails}
        
        dependency_trail = None 
        if settings.relative_parent_object in bpy.data.objects:
            parent_object = bpy.data.objects[settings.relative_parent_object]
            if isinstance(parent_object.data,bpy.types.Armature) and len(settings.relative_parent_bone) > 0:
                if settings.relative_parent_bone in valid_dependency_targets:
                    dependency_trail = valid_dependency_targets[settings.relative_parent_bone]
            elif settings.relative_parent_object in valid_dependency_targets:
                    dependency_trail = valid_dependency_targets[settings.relative_parent_object]
        
        #there exists a trail for relative parent target, therefore all trails are child of the relative parent
        if (dependency_trail is not None):
            parent_node = trail_lookup[dependency_trail.target_name]
            for i in reversed(range(0,len(roots))):
                #print_time(str(i))
                item_trailOp = roots[i]
                item_node = trail_lookup[item_trailOp.target_name]
                
                if parent_node == item_node:
                    continue 

                #print_time('looking at: ' + item_trailOp.target_name)
                parent_node.children.append(item_node) 
                #in the end, roots will be consistent with its definition
                del roots[i]
                
    #print_time('new roots: ' + str([root.target_name for root in roots]))
    #roots can be called in any order
    #only parent-child order must be preserved
    
    def recursive_add_to_update_order(history,update_order,current):
        if current.target_name in history:
            #todo: can print out  cycle by just following the cycling (go through parents) till we get back to same target
            print_time('trail cyclic dependency detected! related to [{0}]'.format(current.target_name))
        else:
            #print_time('inserted into update order: ' + current.target_name)
            history.add(current.target_name)
            update_order.append(current.target_name)

            #print_time('total children: ' + str(len(trail_lookup[current.target_name].children)))
            for child in trail_lookup[current.target_name].children:
                #print_time('onto next child: ' + child.target_name)
                recursive_add_to_update_order(history,update_order,child)
            #print_time('end children for ' + current.target_name)
    update_order = []
    history = set()
    for root in roots:
        #print_time('inserting root: ' + root.target_name)
        recursive_add_to_update_order(history,update_order,trail_lookup[root.target_name])
        
    ordered_trail_callbacks.clear()
    ordered_trail_nodes.clear()
    for target_name in update_order:
        ordered_trail_nodes.append(trail_lookup[target_name])
        ordered_trail_callbacks.append(trail_callbacks[target_name])

    print_conditional(debug_enable_print_func_tags,'reordered trail updates:' + str( update_order))


#without this, scene_update isnt called for trails after file load
#@persistent, althought persistent is useful, just results in obscure bugs due when accidently doing double updates (handle not cleaned up despite being removed..)
def root_trail_ordered_callback(scene,despgraph):
    
    if crash_stop_everything:
        print_time('CSE root trail ordered callback')
        return 


    #func may be called after unregister() called, leading to error due to unregistered classes.
    if unregistered:
        return 
    try:



            
        #print_time(trail_callbacks) 
        print_conditional(debug_enable_print_func_tags ,'>>>>>>>>>>   ordered draw callback start     <<<<<<<<<')
        settings = bpy.context.scene.motion_trail3D_settings
        trail_lookup = {trailOp.target_name : trailOp for trailOp in settings.active_trails}
        
        #without this check, deleted trails will not be found in trail_lookup causing keyError
        undo_deleted_trail = len(trail_lookup) != len(ordered_trail_nodes) 
        for parent_node in ordered_trail_nodes:
            undo_deleted_trail = undo_deleted_trail or (parent_node.target_name not in trail_lookup)
        if undo_deleted_trail:
            print_undocheck('reordering trails, undo caused trail deletion. (or trail data re-added due to redo)')
            #print_time('reordering trails, undo caused trail deletion. (or trail data re-added due to redo)')
            for i in reversed(range(0,len(settings.active_trails))):
                trailOp = settings.active_trails[i]
                target_name = trailOp.target_name 
                #for case where user redos after deactivation trail, so trail data exists but callback has already been removed.
                if target_name not in trail_callbacks:
                    print_undocheck('trail was readded after a redo: ' + trailOp.name)
                    trailOp.is_active=False
                    settings.active_trails.remove(i)
                    
            reorder_trail_updates()
            trail_lookup = {trailOp.target_name : trailOp for trailOp in settings.active_trails}

        for i,parent_node   in enumerate(ordered_trail_nodes):
            parentOp = trail_lookup[parent_node.target_name]
            parentOp.hierarchy_has_updated =False 

        for i,func   in enumerate(ordered_trail_callbacks):
            parent_node = ordered_trail_nodes[i]
            #print_time('executing: ' + parent_node.target_name + '...')
            
            func(scene,despgraph)
            
            parentOp = trail_lookup[parent_node.target_name]
            parentOp.hierarchy_has_updated =parentOp.hierarchy_has_updated or  parentOp.has_updated

            #no need to propagate recursively. When child node is enumerated in the outter loop, then it'll propagate update to its children too before the child reads the value.
            for child_node in parent_node.children:
                childOp = trail_lookup[child_node.target_name]
                #propagate update flag to allow a whole hierarchy chain to update
                childOp.hierarchy_has_updated = childOp.has_updated or parentOp.hierarchy_has_updated 
                #print_time('propagate from {2}[{3}] to child: {0} [{1}]->[{4}]'.format(childOp.target_name, childOp.has_updated,parent_node.target_name,parentOp.hierarchy_has_updated, childOp.hierarchy_has_updated))
            #print_time('..done: ' + parent_node.target_name)
            
        print_conditional(debug_enable_print_func_tags ,'>>>>>>>>>>  END  ordered draw callback start     <<<<<<<<<')
    except Exception as e:
        #print(e)
        import traceback
        msg = traceback.format_exc()
        print_time('[ERROR] : ' + msg)

if debug_crash_search:
    root_trail_ordered_callback = wrap('root callback',root_trail_ordered_callback)
    reorder_trail_updates = wrap('reorder updates',reorder_trail_updates)

def register_trailOp(object_name,target_name):
    settings = bpy.context.scene.motion_trail3D_settings
    data = settings.active_trails.add()
    data.is_active=True 
    data.object_name = object_name
    data.target_name = target_name 

    global nonserialized_undo_tracker
    nonserialized_undo_tracker[target_name] = 0  

    return data 

def unregister_trailOp(target_name):
    settings = bpy.context.scene.motion_trail3D_settings

    index,item = get_registered_trailOp(target_name)
    if index >= 0:
        item.is_active=False
        #note: since we're removing from active_trails, then modal() and draw_callback are the only ones that would catch the disposal
        target_name = item.target_name 

        settings.active_trails.remove(index)
        
        #bugfix:when trail deactivated, other trails that dep. on it will have dep.  flag disabled. Prevents error in render sometimes happening
        for active_trail in settings.active_trails:
            if active_trail.dependency.target_name == target_name:
                active_trail.dependency.is_active = False
    
    global nonserialized_undo_tracker
    if target_name in nonserialized_undo_tracker:
        del nonserialized_undo_tracker[target_name]

def deactivate_trailOp(target_name):
    settings = bpy.context.scene.motion_trail3D_settings

    index,item = get_registered_trailOp(target_name)
    if index >= 0:
        item.is_active=False 
    
def get_registered_trailOp(target_name):
    settings = bpy.context.scene.motion_trail3D_settings
    for i,item in enumerate(settings.active_trails):
        if item.target_name == target_name:
            return i,item 
    return -1,None 

def create_mesh(object_name='object',mesh_name='mesh'):
    data = bpy.data
    scene = bpy.context.scene
    mesh = data.meshes.new(name=mesh_name)
    obj = data.objects.new(name=object_name,object_data=mesh)
    master_collection = bpy.context.view_layer.active_layer_collection.collection
    master_collection.objects.link(obj)

    #scene.objects.active = object
    #object.select=True
    return obj

def matrix_trs(translation,quaternion,scale):
    return Matrix.Translation(translation) @ quaternion.to_matrix().to_4x4() @ Matrix.Scale(scale[0],4,(1,0,0)) @ Matrix.Scale(scale[1],4,(0,1,0)) @ Matrix.Scale(scale[2],4,(0,0,1))
def matrix_scale(scale):
    return Matrix.Scale(scale[0],4,(1,0,0)) @ Matrix.Scale(scale[1],4,(0,1,0)) @ Matrix.Scale(scale[2],4,(0,0,1))

def time_string():
    dt = datetime.datetime.now()
    return str(dt.minute) + ':' +str(dt.second) +':' + str(int(dt.microsecond / 10000))

def create_empty(world,name='Empty'):
    o = bpy.data.objects.new(name, None )
    o.matrix_world = world
    o.show_in_front = True
    o.empty_display_type = 'ARROWS'
    o.empty_display_size = 15
    o.rotation_mode = 'QUATERNION'

    return o

# Use a list to manage depth ranges manually
glDepthRangeBuffer = []
glDepthRange_cur = None  # Default is set to None

def glDepthRange_push(close, far):
    global glDepthRange_cur

    if glDepthRange_cur is None:
        # Assume the default depth range if it's not set
        glDepthRange_cur = (0.0, 1.0)

    # Push the current depth range to the buffer
    glDepthRangeBuffer.append(glDepthRange_cur)
    # Update the current depth range
    glDepthRange_cur = (close, far)

    # Note: Skipping depth range set since it's not available in GPU module
    # If needed, use custom shaders or alternative approaches here

def glDepthRange_pop():
    global glDepthRange_cur

    # Pop the last depth range from the buffer
    if glDepthRangeBuffer:
        glDepthRange_cur = glDepthRangeBuffer.pop()
    else:
        # Reset to default if the buffer is empty
        glDepthRange_cur = (0.0, 1.0)

    # Note: Skipping depth range restore since it's not available in GPU module
    # Reset to None so on the next draw() call, we use the default depth range
    if not glDepthRangeBuffer:
        glDepthRange_cur = None


#port: matrix_to_glBuffer
def matrix_to_glBuffer(matrix):
    # Transpose the matrix to match OpenGL's column-major order
    copy = matrix.transposed()
    # Convert the matrix to a 1D numpy array with 16 elements (4x4 matrix)
    matrix_array = np.array(copy, dtype=np.float32).ravel()
    # Create a buffer from the numpy array
    matrix_buffer = gpu.types.Buffer('FLOAT', (16,), matrix_array.tolist())
    return matrix_buffer

def clamp(value,min_val,max_value):
    return min(max(value,min_val),max_value)

def evaluate_bezier(t,p0,p1,p2,p3):
    return (1*((1-t)**3)*t**0)*p0 +    \
           (3*((1-t)**2)*t**1)*p1 +    \
           (3*((1-t)**1)*t**2)*p2 +    \
           (1*((1-t)**0)*t**3)*p3 
           
def bezier_split(t,control_points):
    
    left_p0,left_p1,left_p2,left_p3 = bezier_split_left(t,control_points)

    reverse_control_points = (control_points[3],control_points[2],control_points[1],control_points[0])
    right_p3,right_p2,right_p1,right_p0 = bezier_split_left((1-t),reverse_control_points)

    #print('left_p3 {0} should equal right_p0 {1}'.format(left_p3,right_p0))
    return (left_p0,left_p1,
            left_p2,left_p3,right_p1,
            right_p2,right_p3)
    #return (original_values[0], leftkey_handle_value,\
    #        mid_left_value,mid_value,mid_right_value, \
    #         rightkey_handle_value, original_values[3])

def bezier_split_left(t,control_points):
    #we use the fact that we can eval the original bezier to get enough equations for the 3 unks (split co, split handle left, p0 handler right)
    #control_points = (keyleft_co[1],keyleft_handle_right[1],keyright_handle_left[1],keyright_co[1])
    p0 = control_points[0]
    p1 = control_points[1]
    p2 = control_points[2]
    p3 = control_points[3]
    
    #ta,tb values arbitrary, only have to be in interval(0,t)
    ta = (1.0/3) * t
    tb = (2.0/3) * t
    Ba = evaluate_bezier(ta,p0,p1,p2,p3)
    Bb = evaluate_bezier(tb,p0,p1,p2,p3)

    ka = ta / t 
    a0 = (1*((1-ka)**3)*(ka**0))
    a1 = (3*((1-ka)**2)*(ka**1))
    a2 = (3*((1-ka)**1)*(ka**2))
    a3 = (1*((1-ka)**0)*(ka**3))
    
    kb = tb / t
    b0 = (1*((1-kb)**3)*(kb**0))
    b1 = (3*((1-kb)**2)*(kb**1))
    b2 = (3*((1-kb)**1)*(kb**2))
    b3 = (1*((1-kb)**0)*(kb**3))
    
    fc = evaluate_bezier(t,p0,p1,p2,p3)
    q1 = Ba - (a2/b2)*Bb - p0 *(a0 - (a2 * (b0 / b2))) - fc * (a3 - (a2 * (b3/b2)))
    q1 = q1 / (a1 - (a2 * (b1/b2)))
    fl = Ba - (a1/b1)*Bb - p0 *(a0 - (a1 * (b0 / b1))) - fc * (a3 - (a1 * (b3/b1)))
    fl = fl / (a2 - (a1 * (b2/b1)))

    return (p0,q1,fl,fc)

def bezier_search_frame(target_frame,p0,p1,p2,p3):
    #assumes bezier is one-one, does not cross itself vertically
    #(means handles don't pass other handles horizontally)
    left = 0
    right = 1
    guess = .5 * (right - left) + left

    #print('target: {0}'.format(target_frame))
    guess_value = evaluate_bezier(guess,p0,p1,p2,p3)
    iterations_limit = 100
    while(iterations_limit > 0):
        iterations_limit = iterations_limit-1

        if (guess_value - target_frame) > .001:
            #too high
            #print('guess: {0:.5f}  guess_value:{1:.5f} is too high. left:{2:.5f} right:{3:.5f}'.format(guess,guess_value,left,right))
            right = guess
            guess = .5 * (right - left) + left
            guess_value = evaluate_bezier(guess,p0,p1,p2,p3)
        
        elif(guess_value - target_frame) < -.001:
            #too low
            #print('guess: {0:.5f}  guess_value:{1:.5f} is too low. left:{2:.5f} right:{3:.5f}'.format(guess,guess_value,left,right))
            left = guess 
            guess = .5 * (right - left) + left
            guess_value = evaluate_bezier(guess,p0,p1,p2,p3)
        else:
            #print('FOUND guess: {0:.5f} guess_value:{1:.5f} target_value:{2:.5f} iterations:{3}'.format(guess,guess_value,target_frame, 100-iterations_limit))
            return guess
    #print('failed to find bezier mu after 100 iterations...')
    return .5

def split_bezier_keys(frame,t_axis_controls,value_axis_controls):

    z = bezier_search_frame(frame,*t_axis_controls) 
    
    #print('frame:{0} z:{1}'.format(frame,z))
    #(left's value, left's handle right, mid's handle left, mid's value, mid's handle right, right's handle left,right's value)
    split_times = bezier_split(z,t_axis_controls)
     
    #z = float(split_times[3] -  keyframe_left.co[0]) /  float(keyframe_right.co[0] -  keyframe_left.co[0])
    split_values = bezier_split(z,value_axis_controls)

    return ((split_times[1],split_values[1]),  #left bezier: p1    
            (split_times[2],split_values[2]),  #left bezier: p2  
            (split_times[3],split_values[3]),  #left bezier: p3  
            (split_times[4],split_values[4]),  #right bezier: p1  
            (split_times[5],split_values[5]))  #right bezier: p2  

def calculate_triplet_control_values(channels,triplet_buffer,channel_index,out_values,out_times):
    #func general enough to be used with any set of channels (rot too)
    #fills out buffers with direct key info and split key info 
   
    #do linear walk, tracking prev valid key.
    #store unfinfished keys
    #when find next valid key, split at each unfinished key.
    #no need to overwrite valid key control values. Just store and use the split handles from the valid key for proceeding unfinished keys
    
    #bug           : for non split keys that occur before any triplet and after all triplets, we don't account for if there is a keyframe outside of the preview range before and after the unsplit keys.
    
    '''
    todo: Q: is it important to have an accurate bezier split?
          A: No. only tangent is useful. Goal is an intuitive 3D-space handle tangent.  Magnitude can be arbitary.  
            ...but as a split varies (modal) the magnitude, the world space x value does change. And we care about world space tangent. Not loacl space tangent..
            So... yeah its important for the intuition?
            ...yet a split doesnt modify the curve at all, despite changing the handle mags..-mid key compensates?

            ..i really dont know if this makes sense. It shouuuld... because the beziers are tangent and representative of the local bezier...
            changing magnitude does not change tangent at frame.
            It only changes the strength of the tangent, how closely the sample points hug the tangent?...ill just have to render it and see..

    Q: I think it should be that the implicit tangent's time needs to align with the time of the valid key's index for the triplet.?
    And if only tangent needs to be maintained... then is there a reason for an accurate split? Its not even rendered intuitively..

    Q: Soo the real goal of all this was to determine a way to associate a column of frame-aligned keys (done: triplets buffer).
     It was also to provide a way to refresh or create/delete control objects based on fcurve changes  by user through graph editor or dopesheet,
        including dragging keys into different triplets..

    Lets assume its cheap to generate triplets buffer over preview range.
    Then we need to link objects to triplets (cheap) and (maybe not necessary?) caclculate ctrl local values for implicit keys to fill those empty triplet components
    '''
    unfinished_triplet_indices = []
    #no channels, do nothing. Caller already filled defaults (recalculate_control_values())
    if channels[channel_index] is None:
        return 

    keyframe_points = channels[channel_index].keyframe_points
    prev_valid_triplet = None
    prev_valid_triplet_index = None   
    cur = None 
    cur_index = 0
    end = len(triplet_buffer)
    if end == 0:
        return 

    #write default values till the first valid triplet
    while(cur_index < end):
        cur = triplet_buffer[cur_index]

        if cur[channel_index] is None:
            unfinished_triplet_indices.append(cur_index)
        else:
            break
        
        cur_index += 1

    #write default value and times
    for unfinished_index in unfinished_triplet_indices:
        unfinished_triplet = triplet_buffer[unfinished_index]
        frame = unfinished_triplet.frame
        default_value = channels[channel_index].evaluate(frame)
        out_values[unfinished_index] = (default_value,default_value,default_value)
        out_times[unfinished_index] = (frame,frame,frame)

    #either at the end of the buffer or at first valid triplet
    prev_valid_triplet = cur 
    prev_valid_triplet_index = cur_index

    if prev_valid_triplet[channel_index] is not None:
        prev_key = keyframe_points[prev_valid_triplet[channel_index]]
        out_times[prev_valid_triplet_index] = (prev_key.handle_left[0],prev_key.co[0],prev_key.handle_right[0])
        out_values[prev_valid_triplet_index] = (prev_key.handle_left[1],prev_key.co[1],prev_key.handle_right[1]) 


    cur_index += 1
    cur_key = None
    while(cur_index < end):
        cur = triplet_buffer[cur_index]

        if cur[channel_index] is not None:

            prev_key = keyframe_points[prev_valid_triplet[channel_index]]
            cur_key = keyframe_points[cur[channel_index]]

            if len(unfinished_triplet_indices) > 0:
                t0,v0 = prev_key.co
                t1,v1 = prev_key.handle_right
                t2,v2 = cur_key.handle_left
                t3,v3 = cur_key.co
                
                unfinished_index = unfinished_triplet_indices[0]
                unfinished_triplet = triplet_buffer[unfinished_index]
                frame = unfinished_triplet.frame

                #potential optimization: since we're splitting sequentially, can start bezier_search_frame with lower bound as prior mu
                split = split_bezier_keys(frame,(t0,t1,t2,t3),(v0,v1,v2,v3))

                valid_time_axis = triplet_buffer[unfinished_index].time_axes[1]
                valid_channel = channels[valid_time_axis]
                #print('using valid axis for frame: ({0},{1},{2})[{3}]'.format(unfinished_triplet[0],unfinished_triplet[1],unfinished_triplet[2],valid_time_axis))
                time_axis_key = valid_channel.keyframe_points[unfinished_triplet[valid_time_axis]]
                valid_lhandle_time = time_axis_key.handle_left[0]
                valid_rhandle_time = time_axis_key.handle_right[0]

                time_lhandle = split[1][0]
                #time_co = split[2][0]
                time_rhandle = split[3][0]

                value_lhandle = split[1][1]
                value_co = split[2][1]
                value_rhandle = split[3][1]

                slope_lhandle = (value_lhandle - value_co) / (time_lhandle - frame)
                slope_rhandle = (value_rhandle - value_co) / (time_rhandle - frame)

                channel_eval_co = channels[channel_index].evaluate(frame=frame)
                extended_value_lhandle = channel_eval_co + slope_lhandle * (valid_lhandle_time - frame)
                extended_value_rhandle = channel_eval_co + slope_rhandle * (valid_rhandle_time - frame)

                #use evaluated co point as origin for implicit handles.
                #since we dont write to them, it doesnt break anything. The important is the world-space tangent which is preserved.
                #the reason we do so is that Blender will avg the channels sample points if the handles overlap.
                #therefore, if it does overlap, then we ensure the rendered handle is at the correct world position.
                out_times[unfinished_index] =  (valid_lhandle_time,frame,valid_rhandle_time) 
                out_values[unfinished_index] = (extended_value_lhandle,channel_eval_co,extended_value_rhandle)


                #reuse split result to split proceeding consecutive unfinished indices
                t0,v0 = split[2]
                t1,v1 = split[3]
                t2,v2 = split[4]
                for k in range(1,len(unfinished_triplet_indices)):
                    unfinished_index = unfinished_triplet_indices[k]
                    unfinished_triplet = triplet_buffer[unfinished_index]
                    frame = triplet_buffer[unfinished_index].frame

                    split = split_bezier_keys(frame,(t0,t1,t2,t3),(v0,v1,v2,v3))

                    valid_time_axis = triplet_buffer[unfinished_index].time_axes[1]
                    time_axis_key = channels[valid_time_axis].keyframe_points[unfinished_triplet[valid_time_axis]]
                    valid_lhandle_time = time_axis_key.handle_left[0]
                    valid_rhandle_time = time_axis_key.handle_right[0]

                    time_lhandle = split[1][0]
                    #time_co = split[2][0]
                    time_rhandle = split[3][0]

                    value_lhandle = split[1][1]
                    value_co = split[2][1]
                    value_rhandle = split[3][1]

                    slope_lhandle = (value_lhandle - value_co) / (time_lhandle - frame)
                    slope_rhandle = (value_rhandle - value_co) / (time_rhandle - frame)

                    channel_eval_co = channels[channel_index].evaluate(frame=frame)
                    extended_value_lhandle = channel_eval_co + slope_lhandle * (valid_lhandle_time - frame)
                    extended_value_rhandle = channel_eval_co + slope_rhandle * (valid_rhandle_time - frame)

                    #use evaluated co point as origin for implicit handles.
                    #since we dont write to them, it doesnt break anything. The important is the world-space tangent which is preserved.
                    #the reason we do so is that Blender will avg the channels sample points if the handles overlap.
                    #therefore, if it does overlap, then we ensure the rendered handle is at the correct world position.
                    out_times[unfinished_index] =  (valid_lhandle_time,frame,valid_rhandle_time) #(split[1][0],split[2][0],split[3][0])
                    out_values[unfinished_index] = (extended_value_lhandle,channel_eval_co,extended_value_rhandle)

                    #reuse split result to split proceeding consecutive unfinished indices
                    t0,v0 = split[2]
                    t1,v1 = split[3]
                    t2,v2 = split[4]
                    #t3,v3 unchanged
                    
            out_times[cur_index] = (cur_key.handle_left[0],cur_key.co[0],cur_key.handle_right[0])
            out_values[cur_index] = (cur_key.handle_left[1],cur_key.co[1],cur_key.handle_right[1]) 

            unfinished_triplet_indices.clear()
            prev_valid_triplet = cur
            prev_valid_triplet_index = cur_index
        else:
            unfinished_triplet_indices.append(cur_index)
        
        cur_index += 1

    #at end of triplet buffer.
    #if unfinished_triplet_indices has elements, then we need to use last prev_valid triplet's value to fill the rest
    #time doesnt matter. Wont be used for time objs since its an implicit key and represents a static point.
    #all lhandle,co,rhandle can also be set to the same value
    for unfinished_index in unfinished_triplet_indices:
        unfinished_triplet = triplet_buffer[unfinished_index]
        frame = unfinished_triplet.frame
        default_value = channels[channel_index].evaluate(frame)
        
        out_values[unfinished_index] = (default_value,default_value,default_value)
        out_times[unfinished_index] = (frame,frame,frame)
        
def append_triplets_from_channel(keyframe_points,valid_points,triplet_buffer,channel_index,triplet_size=3):
    #func general enough to be used with any set of channels (rot too), builds the triplet buffer to account for all previously appended triplets.
    #memory: optimization: assuming python doesn't delete memory when lsit cleared, then
    #we only would need to pool TripletItem instances
    triplet_index = 0
    valid_key_index = 0
    valid_len = len(valid_points)
    triplet_len = len(triplet_buffer)
    

    '''
    -case where new triplet item creation means prior axes were filled with None, therefore we have to calculate those splits...
    if we store running bezier handles and changes due to split, that removes need to search buffer for valid handle to split with.
    then after all appending done for all axes, we overwrite handles for valid triplets only
        [updated: we don't. We shouldn't due to that changing the valid handles and associated curve.]
    '''

    prev_valid_triplet = None 
    split_occurs = False
    while(valid_key_index < valid_len and triplet_index < triplet_len):
        key_index = valid_points[valid_key_index]
        key = keyframe_points[key_index]
        frame = round(key.co[0])
        item = triplet_buffer[triplet_index]
        
        #if matching frame, then link ykey with the triplet
        if frame == item.frame:

            item[channel_index] = key_index

            if split_occurs:
                item.time_axes[0] = channel_index

            triplet_index = triplet_index+1
            valid_key_index = valid_key_index+1
            prev_valid_triplet = item
            split_occurs=False
            
        #there was no triplet created for an xKey at this frame
        elif frame < item.frame:
            #insert new triplet, xKey does not exist at same frame
            new_item = TripletItem(frame =frame,time_axis=channel_index,size=triplet_size)
            triplet_buffer.insert(triplet_index,new_item)
            new_item[channel_index] = key_index 

            #since we're creating an implicit keys, its visually more useful to change last valid triplet to use this channel as time axis. (if it hasn't been written yet)
            if(prev_valid_triplet is not None):
                prev_valid_triplet.time_axes[2] = channel_index
                prev_valid_triplet = None
                
            split_occurs = True
            #note that we don't increment by 2.
            #this is so that the current item is check again in the next iteration
            triplet_index = triplet_index+1
            valid_key_index = valid_key_index+1
            triplet_len = triplet_len + 1

        #this yKey doesnt align with the current triplet, search for one that it does or whether to create a new triplet
        else:
            while((frame > item.frame ) and (triplet_index < (triplet_len-1))):
                triplet_index = triplet_index+1
                item = triplet_buffer[triplet_index]
            #if not found, then triplet_index = end, thus outter loop also ends
            if (frame > item.frame) and (triplet_index >= triplet_len - 1):
                break

    #by now, either key_index = end and/or triplet_index = end
    #if key_index = end then all possible triplets for ychannel has been created.
    #if key_index != end and triplet_index == end, then we need to create a triplet foreach remaining ykey. There are no matching triplets existing. 
    #   -remaining yKey frames > all triplet frames
    #if key_index != end and triplet_index != end is not a possibility.
    #Therefore, we only need to handle 2nd case.
    start = valid_key_index
    for valid_key_index in range(start,valid_len):
        key_index = valid_points[valid_key_index]
        key = keyframe_points[key_index]
        frame = round(key.co[0])
        #insert new triplet, xKey does not exist at same frame
        new_item = TripletItem(frame =frame,time_axis=channel_index,size=triplet_size)
        triplet_buffer.append(new_item)
        new_item[channel_index] = key_index
def vec_to_tuple(vec):
    return (vec.x,vec.y,vec.z)
def get_valid_keys(keyframe_points,out_list,frame_start,frame_end):
    for i,keyframe_point in enumerate(keyframe_points):
        if round(keyframe_point.co[0]) >= frame_start and round(keyframe_point.co[0]) <= frame_end:
            out_list.append(i)

def obj_hide_get(obj):
    return obj.hide_get() or obj.hide_viewport 

def is_ctrl_used(obj):
    #assumes user doesn't hide/unhide controls themselves
    #order matters. is_ctrl_used may be called with non-object type which doesn't have obj.hide_get()
    #but if its not a contrl object, then it fails the first anyways.
    return  (((TAG_triplet_index in obj) and obj[TAG_triplet_index] != None)) and not (obj_hide_get(obj) or obj.hide_select) 
def vec_distance(a,b):
    #...(a-b).magnitude is broken?
    offsetx = a.x - b.x
    offsety = a.y - b.y 
    offsetz = a.z - b.z
    offsetmag = math.sqrt(offsetx ** 2 + offsety**2 + offsetz**2)
    return offsetmag
tmp_key = [0,0,0]
def tupled_key(key):
    global tmp_key 
    tmp_key[0] = key.handle_left
    tmp_key[1] = key.co
    tmp_key[2] = key.handle_right 
    
    return tmp_key

def is_handle_type_editable(handle_type):
    return handle_type in {'FREE','ALIGNED'}
def align_right_handle(key):
    
    # and not active_trail_data.key_objects[2][triplet_index].select):
    if key.handle_left_type == 'ALIGNED' and key.handle_right_type == 'ALIGNED':
        co = Vector(key.co)
        left = Vector(key.handle_left)
        #limit aligned handles to have frame time = 1 so the slope is defined.
        left_time_offset = (co[0] - left[0])
        
        if abs(left_time_offset) < 1:
            key.handle_left = (key.co[0] - 1,key.handle_left[1])
            left_time_offset = 1
        right_time_offset = key.handle_right[0] - co[0]
        if abs(right_time_offset) < 1:
            right_time_offset = 1

        tangent_per_x = (co-left) * (1.0/left_time_offset)
        handle_right = co +  tangent_per_x * right_time_offset

        key.handle_right = (key.co[0] + right_time_offset,handle_right[1])
        key.select_right_handle = True 
def align_left_handle(key):
    
    if key.handle_right_type == 'ALIGNED' and key.handle_left_type == 'ALIGNED':
            co = Vector(key.co)
            right = Vector(key.handle_right)
            right_time_offset = (co[0] - right[0])
            
            if abs(right_time_offset) < 1:
                key.handle_right = (key.co[0] + 1,key.handle_right[1])
                right_time_offset = -1
            left_time_offset = key.handle_left[0] - co[0]
            if abs(left_time_offset) < 1:
                left_time_offset = -1
            tangent_per_x = (co-right) * (1.0/right_time_offset)
            handle_left = co +  tangent_per_x * left_time_offset
            
            key.handle_left = (key.co[0] + left_time_offset,handle_left[1])
            key.select_left_handle = True 
def offset_left_handle(key,co_offset):
    #move handles with co if they're aligned
    #this doesn't duplicate Blender behaviour, don't know why
    #dont sync move them if the others were transformed too
    if key.handle_left_type == 'ALIGNED':
        key.select_left_handle = True 
        key.handle_left = (key.handle_left[0], key.handle_left[1] + co_offset)
def offset_right_handle(key,co_offset):
    #move handles with co if they're aligned
    #this doesn't duplicate Blender behaviour, don't know why
    #dont sync move them if the others were transformed too
    if key.handle_right_type == 'ALIGNED':
        key.select_right_handle = True 
        key.handle_right = (key.handle_right[0], key.handle_right[1] + co_offset)
    

def debug_print_to_file_init():
    global debug_print_to_file_initialized
    if not debug_print_to_file_initialized:
        debug_print_to_file_initialized = True 
        with(open(debug_print_to_file_path,'w')):
            pass 
def print_wrapped(msg):

    #yes, its written to file on every print, which is expected to be slow.
    #used only when looking for crashes.
    if debug_print_to_file:
        debug_print_to_file_init()
        with open(debug_print_to_file_path,'a') as file:
            print(msg,file=file)
    else:
        print(msg)

time_of_last_print = datetime.datetime.now()
def print_time(msg):
    global  time_of_last_print 
    if (datetime.datetime.now() - time_of_last_print).total_seconds() >= .5:
        print()
    time_of_last_print = datetime.datetime.now()

    if not isinstance(msg,str):
        msg = str(msg)
    
    print_wrapped(f'[{time_string()}] {msg}')

def print_conditional(condition,msg):
    if condition:
        
        if not isinstance(msg,str):
            msg = str(msg)
            
        print_time(msg)
def print_undocheck(msg):
    if debug_print_undo:
    
        if not isinstance(msg,str):
            msg = str(msg)

        print_time(msg)


#endregion

'''END Utility functions'''
'''BEGIN Profiling''' 
#region
profile = False 
def profile_wrap_functions(obj,excluded_functions,collected_func_ids):
    
    collected_ids = []
    profiler_items = []
    object_methods = [method_name for method_name in dir(obj) if method_name not in excluded_functions and callable(getattr(obj, method_name)) and not method_name.startswith('__')]
    for method_name in object_methods:
        method = getattr(obj, method_name)
        #print('method: ' + method_name)

        profiler_item = ProfilerFunctionInfo(method_name)
        profiler_items.append(profiler_item)

        profiled_method = profiler_item.wrap(method)
        setattr(obj,method_name,profiled_method)

        if method_name in collected_func_ids:
            collected_ids.append(profiler_item.id)
            
    return profiler_items,collected_ids
profiler_func_ID = 0
def profiler_new_func_id():
    global profiler_func_ID
    profiler_func_ID += 1
    return profiler_func_ID
class ProfilerStack():
    call_stack = [] 

    def begin_call(self,profiler_func):
        call_stack = self.call_stack
        if len(call_stack) > 0:
            parent_call = call_stack[-1]
            
            nested_call = None
            if profiler_func.id not in parent_call.inclusive_nested_calls:
                
                nested_call = parent_call.inclusive_nested_calls[profiler_func.id] = ProfilerFunctionInfo(profiler_func.name)
                #need a unique ID for end_call() 
                #nested_call.id = -profiler_func.id #for debugging purposes, to know item is a nested call and never actually directly used
            else:
                nested_call = parent_call.inclusive_nested_calls[profiler_func.id]

            call_stack.append(nested_call)
        else:
            call_stack.append(profiler_func)
            

    def end_call(self,profiler_func,delta_time):
        
        call_stack = self.call_stack

        if len(call_stack) > 1:
            parent_call = call_stack[-2]
            nested_call = parent_call.inclusive_nested_calls[profiler_func.id]#call_stack[-1]#
            #original func never called by nested, so we have to track it here 
            #note that nested calls and duration is accumulative over all parent calls
            nested_call.calls += 1
            nested_call.duration += delta_time

        del self.call_stack[-1]

profiler_stack = ProfilerStack()

class ProfilerFunctionInfo():
    #can extend this to account for nested calls, but thats not needed atm
    def __init__(self,func_name):
        self.name = func_name
        self.calls = 0
        self.duration = 0
        self.id = profiler_new_func_id()
        self.inclusive_nested_calls = {}
    
    def wrap(self,func):
        
        
        def wrapped_func(*args, **kwargs):
            profiler_stack.begin_call(self)

            start_time = time.perf_counter_ns() / (1000.0 * 1000.0) 
            result = func(*args,**kwargs)
            delta_time = (time.perf_counter_ns() / (1000.0 * 1000.0) ) - start_time 

            self.calls += 1 
            self.duration += delta_time #nano to milliseconds

            profiler_stack.end_call(self,delta_time)
            
            return result 

        return wrapped_func
        

def print_profiler_functions(funcs,parent_func_ids,tabs=''):
    
    print('-----------------')
    #print('{0:<30} {1:<10} {2:<13} {3:15} {4:<10} {5:<10}'.format('func','calls','duration(ms)','avg duration'))#,'%calls','%duration'))
    print('{0:<40} {1:<10} {2:<13} {3:15}'.format('func','calls','duration(ms)','avg duration'))

    total_calls =0.0
    total_duration = 0.0
    for func in funcs:
        total_calls+=func.calls 
        total_duration += func.duration 
    
    for parent_func in reversed(funcs):
        if parent_func.id in parent_func_ids:
            print()
            print_profiler_function(parent_func, total_calls,total_duration,tabs)
    
def print_profiler_function(func,total_calls,total_duration, tabs=''):
    print('{0:<40} {1:<10} {2:<13.3f} {3:<15.3f}'.format(tabs + func.name,func.calls,func.duration,(func.duration/func.calls if func.calls > 0 else  0)))

    funcs = [func for func in func.inclusive_nested_calls.values()]
    funcs.sort(key=lambda item: item.duration)

    #with nested:
    #   can obtain duration for call which excludes nested calls
    #   can get total times a nested call is invoked per parent call, leads to a better avg call time per render step.
    
    for nested_func in reversed(funcs):
        print_profiler_function(nested_func, -1,-1,tabs+'-')
#endregion
'''END Profiling'''

def context_override_area(context, area_type, region_type='WINDOW'):
    '''
    DOPESHEET_EDITOR, VIEW_3D, EMPTY, TIMELINE, GRAPH_EDITOR,
    NLA_EDITOR, IMAGE_EDITOR, CLIP_EDITOR, SEQUENCE_EDITOR
    NODE_EDITOR, TEXT_EDITO, LOGIC_EDITOR, PROPERTIES,
    OUTLINER, USER_PREFERENCES, INFO, FILE_BROWSER, CONSOLE

    regions:
    ‘WINDOW’, ‘HEADER’, ‘CHANNELS’, ‘TEMPORARY’, ‘UI’, ‘TOOLS’, ‘TOOL_PROPS’, ‘PREVIEW’
    '''
    info = None
    for window in bpy.context.window_manager.windows:
        screen = window.screen

        for area in screen.areas:
            if area.type == area_type:
                for region in area.regions:
                    if region.type == region_type:
                        info = (window, screen, area, region)

    if info is not None:
        context_override = ContextOverride(context)
        context_override.window, context_override.screen, context_override.area, context_override.region =info
        
        return context_override
    else:
        return None
class ContextOverride(dict):
    '''
    allows me to treat context overrides the same as non overrides:

        ctx0 = Context_Override(context.copy())
        #works
        obj = ctx0.active_object
        #error
        obj = context.copy().active_object

        just be careful to avoid overwriting existing dictionary attributes
    '''
    def __init__(self, context, *args, **kwargs):
        super(ContextOverride, self).__init__(*args, **kwargs)
        self.__dict__ = self
        self.update(context.copy())
class TrailChannelsData():
    def __init__(self,mode,ptr_channels,frame_start,frame_end):
        #this stored mode not used for anything except debug checks
        self.mode=  mode
        #should I allwo for changing rot mode over time?
        self.total_channels = total_channels = len(ptr_channels)
        #for loc, size=3, for rot, size=4 if AxisAngle/Quatenion, size=3 if euler.
        self.triplet_buffer = []
        #[channel_index][triplet_index] = (lhandle value/time,co v/t, rhandle v/t)
        self.key_values_per_channel =  [[] for _ in range(0,total_channels)] 
        self.key_times_per_channel =   [[] for _ in range(0,total_channels)] 
        #[channel_index][frame_index] = channel evaluated value or a default if channel does not exist
        self.sample_values_per_channel = [([None] * (frame_end-frame_start+1)) for _ in range(0,total_channels)] 
        self.key_objects = KeysObjectBuffer(0) 
        self.key_time_objects = KeysObjectBuffer(0) 
        self.updated_objects = UpdatedObjectsBuffer()
        self.updated_time_objects = UpdatedObjectsBuffer()
        #redraw func needs to know when time objects begin and end being xformed 
        #on begin, the initial time is stored for the corresponding key control
        #on during and end, the offset from initial time is calculated and written but the initial time is unaffected.
        self.prev_updated_time_objects = UpdatedObjectsBuffer() 
        self.moved_time_objects = TimeObjectDragBuffer(0)
        self.ptr_channels = ptr_channels
        self.channels = [None] * total_channels
        #track total keys. If changed, recalc triplet buffer
        self.total_keys = [0] * total_channels
        self.frame_start,self.frame_end=frame_start,frame_end 
        self.success_deref_channels = False 
        #? self.worlds? is it only ever used to set ctrrl worlds? in that case, can leave to specific writes for loc/rot?
        #self.object_pool = #... since recalc uses obj pool's in_use size..
        if debug_crash_search:
            debug_wrap_func_exec(self,{})
    
    def clear_updated(self):
        self.updated_objects.clear()
        self.updated_time_objects.clear()
    def clear_key_objects(self):
        key_objects =self.key_objects
        key_time_objects =self.key_time_objects
        
        for i in range(0,3):
            key_objects.ptr_grouped[i].clear()
            key_time_objects.ptr_grouped[i].clear()
            key_objects.grouped[i].clear()
            key_time_objects.grouped[i].clear()
        
    def deref(self):
        self.updated_objects.deref()
        self.updated_time_objects.deref()
        self.prev_updated_time_objects.deref()
        self.key_time_objects.deref()
        self.key_objects.deref()   

    def deref_channels(self):
        #as is
        channels = self.channels 
        total_keys =self.total_keys
        valid_channels_changed = False 

        for channel_index,ptr_channel in enumerate(self.ptr_channels):
            pre_channel_instance = channels[channel_index] 
            pre_total_keys = total_keys[channel_index]

            channels[channel_index] = None 
            total_keys[channel_index] = None 
            if ptr_channel.exists():
                channels[channel_index] = ptr_channel.deref() 
                total_keys[channel_index] = len(channels[channel_index].keyframe_points)

            #if total_keys[channel_index] != pre_total_keys:
            #    print_time('channel deref failed. Key count change.')
            #key total count fixes an error that gets raised when user drags location key over another which deletes a key.
            valid_channels_changed = valid_channels_changed or (pre_channel_instance !=  channels[channel_index]) or (total_keys[channel_index] != pre_total_keys)
        
        self.success_deref_channels = not valid_channels_changed
        return self.success_deref_channels 
    
    def read_sample_points(self,default_values):
        '''this does not rely on the triplet buffer, so it can be called as long as channels have been deref()-ed'''
        #using channel.evaluate also takes into account fcurve modifiers.
        #consider: read_sample_points() no need to be in this class? only used for location data.. and even then, the tracking data calculates the same data anways..
        frame_start,frame_end = self.frame_start,self.frame_end
        channels = self.channels 
        sample_values_per_channel = self.sample_values_per_channel
        for channel_index,channel in enumerate(channels):
            values = sample_values_per_channel[channel_index]
            if channel:
                for i in range(frame_start,frame_end+1):
                    values[i-frame_start] = channel.evaluate(frame=i)
            else:
                default_value = default_values[channel_index]#self.target.location[channel_index]
                for i in range(frame_start,frame_end+1):
                    values[i-frame_start] = default_value

    def get_triplet_frame_index(self,triplet_index,control_type):
        
        triplet_buffer = self.triplet_buffer
        ctrl_times_per_channel = self.key_times_per_channel
        frame_start,frame_end = self.frame_start,self.frame_end

        #we use ctrl_times_per_channel just as a simple way to account for possible None axis indices in triplet
        #no need to check if index is None to get frame.
        frame_axis = triplet_buffer[triplet_index].time_axes[control_type]
        frame = int(ctrl_times_per_channel[frame_axis][triplet_index][control_type])
        return  clamp(frame,frame_start,frame_end) - frame_start

    def get_timeKey_from_triplet(self,triplet_index,control_type):
        triplet_buffer = self.triplet_buffer 
        channels = self.channels 
        #print('buffer[{0}], triplet[{1}]'.format(len(triplet_buffer),triplet_index))
        triplet = triplet_buffer[triplet_index] 
        time_axis = triplet.time_axes[control_type]
        #no check for existing channel since triplet time axis only ever references a valid channel
        keyframe_points = channels[time_axis].keyframe_points
        key_index = triplet[time_axis]
        return keyframe_points[key_index]

    def process_newly_moved_time_ctrls(self):
        
        #For stability, need to track store and initial time and obj position.
        #store initial times for associated keys of updated time objects
        #store initial positions for associated time objects
        #both used afterward to determine a stable offset for changing key times when dragging time objects
        updated_time_objects = self.updated_time_objects
        prev_updated_time_objects = self.prev_updated_time_objects
        moved_time_objects = self.moved_time_objects

        for obj in  updated_time_objects.co:
            prev_updated_objects = prev_updated_time_objects.co
            #only store data for newly updated objects
            if obj not in prev_updated_objects:
                #print('inside')
                triplet_index = obj[TAG_triplet_index]
                
                #offset handles along with co
                moved_time_objects.initial_times.left[triplet_index] =  self.get_timeKey_from_triplet(triplet_index,0).handle_left[0]
                moved_time_objects.initial_times.right[triplet_index] =tmp =  self.get_timeKey_from_triplet(triplet_index,2).handle_right[0]
                
                #store nonloc handle offsets 
                #so dragging co preserves the offset at time of drag instead of at time of trail init()
                #for sync_channel in self.sync_collection.channels:
                #    if not sync_channel.channel.lock and sync_channel.is_synced_to(triplet_index):
                #        sync_info = sync_channel.info_from_triplet[triplet_index]
                #        dst_key = sync_info.dst_key
                #        sync_info.lhandle_offset = dst_key.handle_left[0]  - dst_key.co[0]
                #        sync_info.rhandle_offset = dst_key.handle_right[0] - dst_key.co[0]


        for control_type,ptr_objects in enumerate(updated_time_objects.ptr_grouped):
            for ptr_obj in ptr_objects:
                ptr_prev_updated_objects = prev_updated_time_objects.ptr_grouped[control_type]
                #only store data for newly updated objects
                if ptr_obj not in ptr_prev_updated_objects:
                    ptr_prev_updated_objects.add(ptr_obj)
                    obj = ptr_obj.deref()
                    triplet_index = obj[TAG_triplet_index]
                    #print_time('time obj updated: ' + ptr_obj.name + ' index: ' +str(triplet_index))
                    
                    tmp_key = tupled_key(self.get_timeKey_from_triplet(triplet_index,control_type))
                    raw_frame =  tmp_key[control_type][0]
                    
                    moved_time_objects.initial_times.grouped[control_type][triplet_index] = raw_frame
                    moved_time_objects.initial_positions.grouped[control_type][triplet_index] = obj.matrix_world.to_translation().copy()

        #deref() added time objects
        prev_updated_time_objects.deref()
    def process_moved_time_ctrls(self,context,region=None,rv3d=None):
        
        updated_time_objects = self.updated_time_objects
        moved_time_objects = self.moved_time_objects
        triplet_buffer = self.triplet_buffer 
        channels = self.channels 
        frame_start,frame_end = self.frame_start,self.frame_end
        total_channels = self.total_channels

        #apply time-object changes to fcurve-key handles.
        #time offsets based on screen left to right for increasing frame offset.
        if not region:
            region = context.region
        if not rv3d:
            rv3d = context.region_data
        triplet_len = len(triplet_buffer)
    
        #if len(updated_time_objects.grouped[0]) > 0:
        #    print_time('dfasf ')

        #    for k in self.triplet_buffer:
        #        k.display()
        for control_type,updated_objects in enumerate(updated_time_objects.grouped):
            for obj in updated_objects:
                #print('up')
                triplet_index = obj[TAG_triplet_index]
                triplet = triplet_buffer[triplet_index]
                
                initial_time = moved_time_objects.initial_times.grouped[control_type][triplet_index]
                initial_position = moved_time_objects.initial_positions.grouped[control_type][triplet_index]

                obj_screen = bpy_extras.view3d_utils.location_3d_to_region_2d(region,rv3d,obj.matrix_world.to_translation() )
                initial_obj_screen = bpy_extras.view3d_utils.location_3d_to_region_2d(region,rv3d,initial_position)
                
                #print_time(f'init:{initial_obj_screen} cur:{obj_screen}')
                if (obj_screen is None) or (initial_obj_screen is None):
                    continue
                screen_offset = obj_screen - initial_obj_screen
                time_axis = Vector((1,0))
                
                #by truncating to int(..), dragged co time objects do not change the position of co (due to frame sampling of co being unaligned with frame)
                #if co was aligned with frame, it remains aligned
                #if co was unaligned , it remains unaligned
                time_offset = round(time_axis.dot( screen_offset) / 25)
                new_time = round(initial_time +  time_offset)
                
                #prevent dragging key co's past adjacent keys to prevent accidental overwrites
                #note, blender already prevents L/RHandles from crossing associated key, so L/R_triplet_index are fine 
                left_triplet_index =  triplet_index - 1  
                can_clamp_left = left_triplet_index >=0 
                left_key_time = round( self.get_timeKey_from_triplet(left_triplet_index,1).co[0]) if can_clamp_left else new_time
                #co will not be able to overlap adjacent co
                #handles will be able to overlap adjacent co
                left_clamp_offset = 1 if control_type == 1 else 0
                
                right_triplet_index = triplet_index + 1 
                can_clamp_right  = right_triplet_index < triplet_len
                right_key_time = round( self.get_timeKey_from_triplet(right_triplet_index,1).co[0]) if can_clamp_right else new_time
                right_clamp_offset = -1 if control_type == 1 else 0

                if (new_time <= left_key_time and can_clamp_left):
                    new_time = left_key_time + left_clamp_offset
                elif (new_time >= right_key_time and can_clamp_right):
                    new_time = right_key_time + right_clamp_offset

                if control_type==1:
                    new_time = clamp(new_time,frame_start,frame_end)
                else:
                    
                    for axis in range(0,total_channels):
                        channel = channels[axis]
                        if (triplet[axis] is not None) and not channel.lock:
                            key = channel.keyframe_points[triplet[axis]]

                            if key.handle_left_type == 'ALIGNED' and control_type == 0:
                                new_time = min(new_time,round(key.co[0]) - 1)

                                co = Vector(key.co)
                                handle = Vector(key.handle_left)
                                #limit aligned handles to have frame time = 1 so the slope is defined.
                                handle_time_offset = (co[0] - handle[0])
                                if int(abs(handle_time_offset)) < 1:
                                    pass #although it seems like we do nothing, new_time still offset from co by 1 and Blender aligns adj handle tangent to be frame offset by 1 too
                                else:
                                    #preserve tangent by moving handle along it
                                    new_time_offset = new_time - handle[0]
                                    tangent_per_x = (co - handle) * (1.0/handle_time_offset)
                                    handle += tangent_per_x * new_time_offset
                                    key.handle_left = (key.handle_left[0],handle[1])

                            if key.handle_right_type == 'ALIGNED' and control_type == 2:
                                new_time = max(new_time,round(key.co[0]) + 1)
                            
                                co = Vector(key.co)
                                handle = Vector(key.handle_right)
                                #limit aligned handles to have frame time = 1 so the slope is defined.
                                handle_time_offset = (handle[0] - co[0])
                                if int(abs(handle_time_offset)) < 1:
                                    pass #although it seems like we do nothing, new_time still offset from co by 1 and Blender aligns adj handle tangent to be frame offset by 1 too
                                else:
                                    #preserve tangent by moving handle along it
                                    new_time_offset = new_time - handle[0]
                                    tangent_per_x = (handle - co) * (1.0/handle_time_offset)
                                    handle += tangent_per_x * new_time_offset
                                    key.handle_right = (key.handle_right[0],handle[1])
                
                #print_time(str(new_time))
                time_offset = int(new_time-initial_time)

                #if co selected, also offset handles
                #todo: this should be optional
                #todo: cleanup: make func to do general time drag. Aferward, iterate through cos to handle this code. However, its unlikely that user drags many time objs at the same time, so its not much of an optimization.
                if control_type==1:
                    initial_time_left = round(moved_time_objects.initial_times.grouped[0][triplet_index])
                    initial_time_right = round(moved_time_objects.initial_times.grouped[2][triplet_index])


                    new_left_time = initial_time_left + time_offset
                    if(new_left_time < left_key_time and can_clamp_left):
                        new_left_time = left_key_time
                    
                    new_right_time = initial_time_right + time_offset
                    if((new_right_time - right_key_time) > -.5 and can_clamp_right):
                        new_right_time = right_key_time
                
                    #no need to mirror alignment code for left, blender handles this fine. Right handle is exception..
                    #leave outside above clamp to slow losing/leaking handle value 
                    for axis in range(0,total_channels):
                        channel = channels[axis]
                        if (triplet[axis] is not None) and not channel.lock:
                            key = channel.keyframe_points[triplet[axis]]
                            if key.handle_right_type == 'ALIGNED':
                                co = Vector(key.co)
                                handle = Vector(key.handle_right)
                                #bug:doesn't work for left handle...when co offset moves left handle past boundary..

                                #limit aligned handles to have frame time = 1 so the slope is defined.
                                #note: init_times for handles are based on the first existing, non generated from split, axis. 
                                #so if X axis has offset=1, but Z axis has 0, then if we don't account for Z, we'll run into div by 0=moving_handle_time_offset 
                                #handle_time_offset = abs(initial_time - initial_time_right) #why did I use this before??
                                handle_time_offset = abs(co[0] - handle[0])
                                #print_time('time offset {0}'.format(handle_time_offset))
                                #print_time('R time offset from CO: {0}, co_init:{1} r_init:{2}'.format(handle_time_offset,initial_time,initial_time_right))
                                #todo:bug: still prob of when user does move aligned handle to timeoffset=0...
                                if int(abs(handle_time_offset)) < 1:
                                    #print_time('0 time offset for handle right')
                                    #bug: somehow 0-slopes are not preserved. This condition will occur once but not again and thus be aligned with the main triplet time axis...subtle bug
                                    #possibly related to: (note in above alignment fix)although it seems like we do nothing, new_time still offset from co by 1 and Blender aligns adj handle tangent to be frame offset by 1 too
                                    pass #assume user wanted a vertical tangent, don't modify
                                else:
                                    #preserve tangent by moving handle along it
                                    new_time_offset_from_co = new_right_time - new_time
                                    #print('new right:{0} new co:{1} original_dist:{2}'.format(new_right_time + time_offset,new_time,handle_time_offset))
                                    #print('offset: ' + str(new_time_offset_from_co))
                                    tangent_per_x = -(co - handle) * (1.0/handle_time_offset)
                                    handle = tangent_per_x * new_time_offset_from_co + co
                                    key.handle_right = (new_right_time,handle[1])
                                    #print(str(new_time_offset_from_co) + "-_" + time_string()) 

                    for axis in range(0,total_channels):
                        channel = channels[axis]
                        if (triplet[axis] is not None) and not channel.lock:
                            key = channel.keyframe_points[triplet[axis]]
                            if key.handle_left_type == 'ALIGNED':
                                co = Vector(key.co)
                                handle = Vector(key.handle_left)
                                handle_time_offset = abs(co[0] - handle[0])
                                if int(abs(handle_time_offset)) < 1:
                                    #print_time('0 time offset for handle left')
                                    #possibly related to: (note in above alignment fix)although it seems like we do nothing, new_time still offset from co by 1 and Blender aligns adj handle tangent to be frame offset by 1 too
                                    pass #assume user wanted a vertical tangent, don't modify
                                else:
                                    #preserve tangent by moving handle along it
                                    new_time_offset_from_co = new_left_time - new_time
                                    tangent_per_x = (co - handle) * (1.0/handle_time_offset)
                                    handle = tangent_per_x * new_time_offset_from_co + co
                                    key.handle_left = (new_left_time,handle[1])
                                    #print(str(new_time_offset_from_co) + "-_" + time_string()) 
                    for axis in range(0,total_channels):
                        channel = channels[axis]
                        if (triplet[axis] is not None)  and not channel.lock:
                            key_control = tupled_key(channel.keyframe_points[triplet[axis]])[0]
                            key_control[0] = new_left_time
                            key_control = tupled_key(channel.keyframe_points[triplet[axis]])[2]
                            key_control[0] = new_right_time
                
                
                for axis in range(0,total_channels):
                    channel = channels[axis]
                    if (triplet[axis] is not None) and not channel.lock:
                        key =channel.keyframe_points[triplet[axis]]
                        key_control = tupled_key(key)[control_type]

                        if (control_type == 0 and is_handle_type_editable(key.handle_left_type)) or\
                           (control_type == 2 and is_handle_type_editable(key.handle_right_type)) or\
                           (control_type == 1):
                            key_control[0] = new_time
                            #print_time('new time: ' + str(new_time))
                        
    def sync_channel_sel_to_ctrls(self,sync_time):
        #select control objects based on changed key control items
        #sync control object selection to match user's grapheditor/dopesheet selection
        #this is just for convenience and intuition
        key_objects = self.key_objects
        key_time_objects = self.key_time_objects
        triplet_buffer = self.triplet_buffer 
        channels = self.channels 

        if not sync_time:
            for control_objects in key_objects.grouped:
                for control_object in control_objects:
                    control_object.select_set(False)

            for channel_index,channel in enumerate(channels):  
                for i,triplet in enumerate(triplet_buffer):
                    if triplet[channel_index] is not None:
                        channel_key_index = triplet[channel_index]
                        keyframe_point = channel.keyframe_points[channel_key_index]
                        #convenience selection of value objects to quickly allow going back and forth from graph editor to view3D.
                        #it would be inconvenient to also select the time objects since those xforms are likely less frequent and
                        #user may only want to modify exclusively value or time objects. For now, default to only auto select value objects.
                        key_objects.left[i].select_set(  key_objects.left[i].select_get()  or keyframe_point.select_left_handle)
                        key_objects.co[i].select_set(    key_objects.co[i].select_get()    or keyframe_point.select_control_point)
                        key_objects.right[i].select_set( key_objects.right[i].select_get()  or keyframe_point.select_right_handle)
        else:
            for control_objects in key_time_objects.grouped:
                for control_object in control_objects:
                    control_object.select_set(False)

            for channel_index,channel in enumerate(channels):
                for i,triplet in enumerate(triplet_buffer):
                    if triplet[channel_index] is not None:
                        channel_key_index = triplet[channel_index]
                        keyframe_point = channel.keyframe_points[channel_key_index]

                        key_time_objects.left[i].select_set( key_time_objects.left[i].select_get()  or keyframe_point.select_left_handle)
                        key_time_objects.co[i].select_set( key_time_objects.co[i].select_get()   or keyframe_point.select_control_point)
                        key_time_objects.right[i].select_set( key_time_objects.right[i].select_get() or keyframe_point.select_right_handle)
    def recalculate_channel_handles(self):
        #print_time('recalc channel handles')
        #if controls don't overwrite handle if restrictive, then is this function still necessary?
            
        #select the curve handles to match controller-object changes
        #note that fcurve key times and values already overwritten from value objects above
        #to delegate handle alignment to Blender, mimic the user's action effects:
        #   -by selecting the modified handle before calling channel.update(), Blender will recalculate them based on their handle type.

        #clear key and handle selections
        channels = self.channels 
        updated_objects = self.updated_objects
        updated_time_objects = self.updated_time_objects
        triplet_buffer = self.triplet_buffer 

        for channel in channels:
            if channel:
                for keyframe_point in channel.keyframe_points:
                    keyframe_point.select_control_point = False
                    keyframe_point.select_left_handle = False
                    keyframe_point.select_right_handle = False
            
            #for sync_channel in self.sync_collection.channels:
            #    for keyframe_point in sync_channel.channel.keyframe_points:
            #        keyframe_point.select_control_point=False
            #        keyframe_point.select_left_handle = False
            #        keyframe_point.select_right_handle = False
            
            #set selection to updated objects
            for obj in updated_objects.left:
                triplet = triplet_buffer[obj[TAG_triplet_index]]
                for channel_index,channel in enumerate(channels):
                    if triplet[channel_index] is not None:
                        keyframe_point = channel.keyframe_points[triplet[channel_index]]
                        keyframe_point.select_left_handle =  obj.select_get()

            for obj in updated_objects.co:
                triplet = triplet_buffer[obj[TAG_triplet_index]]
                for channel_index,channel in enumerate(channels):
                    if triplet[channel_index] is not None:
                        keyframe_point = channel.keyframe_points[triplet[channel_index]]
                        keyframe_point.select_control_point =   obj.select_get()

            for obj in updated_objects.right:
                triplet = triplet_buffer[obj[TAG_triplet_index]]
                for channel_index,channel in enumerate(channels):
                    if triplet[channel_index] is not None:
                        keyframe_point = channel.keyframe_points[triplet[channel_index]]
                        keyframe_point.select_right_handle =   obj.select_get()

            for obj in updated_time_objects.left:
                triplet_index = obj[TAG_triplet_index]
                triplet = triplet_buffer[triplet_index]
                for channel_index,channel in enumerate(channels):
                    if triplet[channel_index] is not None:
                        keyframe_point = channel.keyframe_points[triplet[channel_index]]
                        #print_time(f'selected key: {triplet[channel_index]} left handle')
                        keyframe_point.select_left_handle =   obj.select_get()

                #for sync_channel in self.sync_collection.channels:
                #    if sync_channel.is_synced_to(triplet_index):
                #        keyframe_point = sync_channel.info_from_triplet[triplet_index].dst_key
                #        keyframe_point.select_left_handle =  True
            
            for obj in updated_time_objects.co:
                triplet_index = obj[TAG_triplet_index]
                triplet = triplet_buffer[triplet_index]
                for channel_index,channel in enumerate(channels):
                    if triplet[channel_index] is not None:
                        keyframe_point = channel.keyframe_points[triplet[channel_index]]
                        keyframe_point.select_control_point =   obj.select_get()
                    
                #for sync_channel in self.sync_collection.channels:
                #    if sync_channel.is_synced_to(triplet_index):
                #        keyframe_point = sync_channel.info_from_triplet[triplet_index].dst_key
                #        keyframe_point.select_control_point =  True
                    
            for obj in updated_time_objects.right:
                triplet_index = obj[TAG_triplet_index]
                triplet = triplet_buffer[triplet_index]
                for channel_index,channel in enumerate(channels):
                    if triplet[channel_index] is not None:
                        keyframe_point = channel.keyframe_points[triplet[channel_index]]
                        keyframe_point.select_right_handle =   obj.select_get()
                    
                #for sync_channel in self.sync_collection.channels:
                #    if sync_channel.is_synced_to(triplet_index):
                #        keyframe_point = sync_channel.info_from_triplet[triplet_index].dst_key
                #        keyframe_point.select_right_handle =  True
            
            #sync nonloc channels
            #for sync_channel in self.sync_collection.channels:
            #    channel = sync_channel.channel
            #    if not channel.lock:
            #        for sync_info  in channel.infos:
            #            src_key = self.get_timeKey_from_triplet(sync_info.triplet_index,1)
            #            dst_key = sync_info.dst_key
            #            lhandle_offset = sync_info.lhandle_offset
            #            rhandle_offset = sync_info.rhandle_offset
            #            src_frame = src_key.co[0]

            #            dst_key.handle_left[0] = src_frame + lhandle_offset
            #            dst_key.co[0] = src_frame
            #            dst_key.handle_right[0] = src_frame + rhandle_offset

            
            #Blender will recalculate handles based on alignment and selection
            for i,channel in enumerate(channels):
                if channel:
                    channel.update()
            #for sync_channel in self.sync_collection.channels:
            #    sync_channel.update()
            
    def generate_triplet_buffer(self):
        #generalize: use a set active_ptr_channels instead of location directly 
        #check if triplet buffer needs to be recreated
        #recreate triplet buffer
        #unlink and pool objects
        #re-link objects
        frame_start,frame_end =self.frame_start,self.frame_end 
        channels = self.channels 
        triplet_buffer = self.triplet_buffer
        total_channels = self.total_channels
        
        self.deref_channels()

        valid_keys = []
        for i,channel in enumerate(channels):
            valid_keys.append([])
            if channel:
                get_valid_keys(channel.keyframe_points,valid_keys[i],frame_start,frame_end)

        #generate triplet buffer. Result is ordered by frame.
        #a tripletItem is a triplet of x,y,z key indices into their respective channel.keyframe_points buffer
        triplet_buffer.clear()
        #note, order of iteration doesnt matter
        for channel_index,channel in enumerate(channels):
            if channel:
                append_triplets_from_channel(channel.keyframe_points,valid_keys[channel_index],triplet_buffer,channel_index,total_channels)
        #for triplet in triplet_buffer:
        #    triplet.display()
    def recalculate_control_values(self,default_values):
        out_values_per_channel = self.key_values_per_channel
        out_times_per_channel = self.key_times_per_channel
        triplet_buffer = self.triplet_buffer
        triplet_len = len(triplet_buffer)
        total_channels = self.total_channels
        channels = self.channels 
        
        for i in range(0,total_channels):
            out_values,out_times =out_values_per_channel[i],out_times_per_channel[i]
            out_values.clear()
            out_times.clear()
            default_value = default_values[i] 
            for _ in range(0,triplet_len):
                out_values.append((default_value,default_value,default_value))
                out_times.append((0,0,0))

        for i in range(0,total_channels):
            out_values,out_times =out_values_per_channel[i],out_times_per_channel[i]
            calculate_triplet_control_values(channels,triplet_buffer,i,out_values,out_times)

class Pool():
    #alloc_func should accept no args
    #dealloc_func should accept object being deallocated
    def __init__(self,item_init_func,alloc_func, dealloc_func,realloc_func,capacity=8):
        self.in_use = 0
        self.capacity = capacity
        self.item_init_func = item_init_func
        self.alloc_func = alloc_func
        self.dealloc_func = dealloc_func
        self.realloc_func = realloc_func
    
        self.buffer = [None] * capacity
        for i in range(0,capacity):
            self.buffer[i] = alloc_func()

    #occurs when undo/redo readds deleted object to ctrl root
    def realloc(self,item):
        self.buffer.append(self.realloc_func(item))
        if len(self.buffer) != self.capacity:
            #print('cap change!: buffer:{0} from {1}'.format(len(self.buffer),self.capacity))
            self.capacity = len(self.buffer)

    def alloc(self):
        in_use,capacity,buffer = self.in_use,self.capacity,self.buffer
        item_init_func,alloc_func, dealloc_func = self.item_init_func,self.alloc_func,self.dealloc_func
        
        #print(f'in Use:{in_use}, cap:{capacity} actual_cap:{len(buffer)}...')
            
        if in_use == capacity:

            #print_time('pool cap increase')

            #occurs if user deletes all controls
            new_capacity = capacity * 2

            if new_capacity == 0:
                new_capacity = 8
                buffer += [None] * new_capacity
                #print(f'ZERO BUFFER in Use:{in_use}, cap:{len(buffer)}')
            else:
                buffer += [None] * capacity

            for i in range(capacity,new_capacity):
                buffer[i] = alloc_func()
            capacity = new_capacity
        
        self.capacity=capacity
        result = buffer[in_use]
        self.in_use = in_use+1
        item_init_func(result)

        return result
        
    def dealloc_all(self):
        in_use,capacity,buffer = self.in_use,self.capacity,self.buffer
        alloc_func, dealloc_func = self.alloc_func,self.dealloc_func

        for i in range(0,in_use):
            dealloc_func(buffer[i])
        self.in_use = 0
           
class TimeObjectDragBuffer():
    def __init__(self,length):
        self.initial_times = KeysBuffer(length,default=0)
        self.initial_positions = KeysBuffer(length,default=Vector((0,0,0)))
    def ensure_size(self,size):
        self.initial_times.ensure_size(size)
        self.initial_positions.ensure_size(size)

class KeysObjectBuffer():
    def __init__(self,length,default=None):
        self.ptr_left = [default] * length
        self.ptr_co = [default] * length
        self.ptr_right = [default] * length
        self.ptr_grouped = [self.ptr_left,self.ptr_co,self.ptr_right]
        
        self.left = [default] * length
        self.co = [default] * length
        self.right = [default] * length
        self.grouped = [ self.left,self.co,self.right]
        self.default = default 

        self.world_left = [Vector((0,0,0)) for i in range(0,length)]
        self.world_co = [Vector((0,0,0)) for i in range(0,length)]
        self.world_right = [Vector((0,0,0)) for i in range(0,length)]
        self.world_grouped = [self.world_left,self.world_co,self.world_right]

    def deref(self):
        for i in range(0,len(self.ptr_left)):
            self.left[i] = self.ptr_left[i].deref()
        for i in range(0,len(self.ptr_right)):
            self.right[i] = self.ptr_right[i].deref()
        for i in range(0,len(self.ptr_co)):
            self.co[i] = self.ptr_co[i].deref()
            
    def clear(self):
        self.ptr_left.clear()
        self.ptr_co.clear()
        self.ptr_right.clear()

    def ensure_size(self,size):
        default = self.default
        increase_size = size -  len(self.left)
        
        if increase_size > 0:
            
            for i in range(0,increase_size):
                self.ptr_left.append(default)
                self.ptr_co.append(default)
                self.ptr_right.append(default)
                self.left.append(default)
                self.co.append(default)
                self.right.append(default)
                self.world_left.append(Vector((0,0,0)))
                self.world_co.append(Vector((0,0,0)))
                self.world_right.append(Vector((0,0,0)))

    def __getitem__(self,key):
        return self.grouped[key]
class KeysBuffer():
    def __init__(self,length,default=None):
        self.left = [default] * length
        self.co = [default] * length
        self.right = [default] * length
        self.grouped = [ self.left,self.co,self.right]
        self.default = default 

    def ensure_size(self,size):
        default = self.default
        increase_size = size -  len(self.left)
        
        if increase_size > 0:
            for _ in range(0,increase_size):
                self.left.append(default)
                self.co.append(default)
                self.right.append(default)

    def __getitem__(self,key):
        return self.grouped[key]

class UpdatedObjectsBuffer():
    def __init__(self):
        self.ptr_left = set()
        self.ptr_co = set()
        self.ptr_right = set()
        self.ptr_grouped = [self.ptr_left,self.ptr_co,self.ptr_right]

        self.left = set()
        self.co = set()
        self.right = set()

        self.grouped = [ self.left,self.co,self.right]
    def clear(self):
        self.left.clear()
        self.co.clear()
        self.right.clear()
        self.ptr_left.clear()
        self.ptr_co.clear()
        self.ptr_right.clear()
    def deref(self):
        self.left.clear()
        self.co.clear()
        self.right.clear()
        for ref in self.ptr_left:
            self.left.add(ref.deref())
        for ref in self.ptr_co:
            self.co.add(ref.deref())
        for ref in self.ptr_right:
            self.right.add(ref.deref())
            
    def __getitem__(self,key):
        return self.grouped[key]

class SyncChannelsBuffer():
    
    class SyncKeyInfo():
        def __init__(self,dst_key,triplet_index,lhandle_offset,rhandle_offset):   
            self.dst_key = dst_key
            self.triplet_index = triplet_index
            self.lhandle_offset = lhandle_offset
            self.rhandle_offset = rhandle_offset

        def debug_print(self):
            print('dst_frame:{0} triplet_index:{1} loffset:{2} roffset:{3}'.format(self.dst_key.co[0],self.triplet_index,self.lhandle_offset,self.rhandle_offset))

    class SyncChannel():
        def __init__(self,channel_array_index):
            self.channel_array_index = channel_array_index
            self.channel = None
            self.infos = []
            self.info_from_triplet = {}

        def append(self,dst_key,triplet_index,lhandle_offset,rhandle_offset):
            info = SyncChannelsBuffer.SyncKeyInfo(dst_key,triplet_index,lhandle_offset,rhandle_offset)
            self.infos.append(info)
            self.info_from_triplet[triplet_index] = info
        def update(self):
            self.channel.update()

        def is_synced_to(self,triplet_index):
            return triplet_index in self.info_from_triplet

        def debug_print(self):
            print('channel: {0}[{1}] len({2})'.format(self.channel.data_path,self.channel.array_index,len(self.infos)))
            for info in self.infos:
                info.debug_print()
            print()

    def __init__(self,length):
        self.channels = [None] * length

class TripletItem():
    def __init__(self,frame=None,time_axis=0,size=3):
        self.frame = frame
        #index associate with channel by index
        #value = valid keyframe point index
        #if value=None then channel either does not exist or no key exists for this triplet at self.frame 
        self.indices = [None] * size 
        #index asssociated to handle left/co/right 
        #value = valid channel index to use for control time
        #value never None, there is always a valid channel to use for time.
        self.time_axes = [time_axis] * size

        
    def __getitem__(self,key):
        return self.indices[key]
    def __setitem__(self,key,value):
        self.indices[key] = value
    def display(self):
            print("frame: {0} triplet:{1} time_axes:{2}".format(self.frame, self.indices,self.time_axes))


class IndirectCollection(object):
    
    def __init__(self, name):
        self.name = name
        if not isinstance(self.name,str):
            raise Exception()
    
    def exists(self):
        return self.name in bpy.data.collections

    def deref(self):
        return bpy.data.collections[self.name]

class IndirectObject(object):

    def __init__(self, object_name):
        self.name = object_name
        if not isinstance(self.name,str):
            raise Exception()

    def rename(self,value):
        return self.name 
        #bug: results in error when control moved so ignoring rename till fixed.
        if self.name != value:
            obj = self.deref() 
            old_name = self.name 
            obj.name = value 
            #Blender will rename obj to ensure its unique so we must reread the objects name
            self.name = obj.name 

            print_time('renamed: {0} to {1}'.format(old_name,self.name))
        return self.name 

    def exists(self):
        return self.name in bpy.data.objects 

    def deref(self):
        return bpy.data.objects[self.name]

class IndirectPoseBone(object):
    
    def __init__(self,object_name,bone_name):
        self.object_name = object_name 
        self.bone_name = bone_name
        if not isinstance(self.object_name,str):
            raise Exception()
        if not isinstance(self.bone_name,str):
            raise Exception()
        
    def exists(self):
        return (self.object_name in bpy.data.objects) and (self.bone_name in bpy.data.objects[self.object_name].pose.bones) 

    def deref(self):
        return bpy.data.objects[self.object_name].pose.bones[self.bone_name]
        
class IndirectAction(object):
    
    def __init__(self,name):
        self.name = name
        if not isinstance(self.name,str):
            raise Exception()
        
    def exists(self):
        return self.name in bpy.data.actions
    def deref(self):
        return bpy.data.actions[self.name]
    
class IndirectChannel(object):
    
    def __init__(self,action_name,data_path,array_index):
        self.action_name= action_name
        self.data_path= data_path
        self.array_index= array_index
        if not isinstance(self.action_name,str):
            raise Exception()
        if not isinstance(self.data_path,str):
            raise Exception()
        if not isinstance(self.array_index,int):
            raise Exception()
    
    def exists(self):
        return (self.action_name in bpy.data.actions) and  (bpy.data.actions[self.action_name].fcurves.find(self.data_path,index=self.array_index) != None )

    def deref(self):
        return bpy.data.actions[self.action_name].fcurves.find(self.data_path,index=self.array_index)

class NULL_OT_NULL_OP(bpy.types.Operator):
    bl_idname = "pose.null_op"
    bl_label = "NULL OP"
    bl_options = {'INTERNAL'}

    @classmethod
    def poll(cls,context):
        return False

    def execute(self, context):
        return {'FINISHED'}
        
class POSE_OT_show_hidden_co(bpy.types.Operator):
    bl_idname = "pose.show_hidden_co"
    bl_label = "Show Hidden Co"
    bl_options = {'INTERNAL'}

    def execute(self, context):
        
        settings = bpy.context.scene.motion_trail3D_settings
        settings.show_hidden_co = not settings.show_hidden_co 
        
        return {'FINISHED'}
class POSE_OT_show_hidden_handles(bpy.types.Operator):
    bl_idname = "pose.show_hidden_handles"
    bl_label = "Show Hidden Handles"
    bl_options = {'INTERNAL'}


    def execute(self, context):
        
        settings = bpy.context.scene.motion_trail3D_settings
        settings.show_hidden_handles = not settings.show_hidden_handles 
        
        return {'FINISHED'}
class POSE_OT_show_hidden_time(bpy.types.Operator):
    bl_idname = "pose.show_hidden_time"
    bl_label = "Show Hidden Time"
    bl_options = {'INTERNAL'}

    def execute(self, context):
        
        settings = bpy.context.scene.motion_trail3D_settings
        settings.show_hidden_time = not settings.show_hidden_time 
        
        return {'FINISHED'}
class POSE_OT_Flip_Quaternion_Ipo_Direction(bpy.types.Operator):
    '''[active selection] For selected quaternion keyframe's left handle, co, and right handle, flips the direction of rotation ipo by negating their values'''
    bl_idname = "pose.flip_quaternion_ipo_direction"
    bl_label = "Flip Quaternion Ipo Direction"
    bl_options = {'REGISTER', 'UNDO'}

    @classmethod
    def poll(cls,context):
        return context.active_object and context.active_object.animation_data and context.active_object.animation_data.action 

    def execute(self, context):
        
        action = context.active_object.animation_data.action 

        channels = None 
        if context.mode == 'POSE':
            pose_bone = context.active_pose_bone
            data_path =  'pose.bones["{0}"].rotation_quaternion'.format(pose_bone.name)
            channels = [action.fcurves.find(data_path,index=i) for i in range(0,4) ]
        else:
            channels = [action.fcurves.find('rotation_quaternion',index=i) for i in range(0,4)]
        
        for channel in channels:
            if (channel is not None )and( not channel.lock) and (not channel.hide):
                
                for keyframe in channel.keyframe_points:
                    if keyframe.select_left_handle:
                        keyframe.handle_left = (keyframe.handle_left[0],-keyframe.handle_left[1])
                        
                    if keyframe.select_control_point:
                        keyframe.co = (keyframe.co[0],-keyframe.co[1])
                        
                    if keyframe.select_right_handle:
                        keyframe.handle_right = (keyframe.handle_right[0],-keyframe.handle_right[1])
                channel.update()
        context.scene.frame_set(context.scene.frame_current)
        return {'FINISHED'}

class POSE_OT_CreateAxesTrackingPoints(bpy.types.Operator):
    '''Create Axes Tracking points'''
    bl_idname = "pose.custom_motion_trail_create_axes_tracking_points"
    bl_label = "Create Axes Tracking Points"
    bl_options = {'REGISTER', 'UNDO'}

    is_bone : BoolProperty('Is Bone',default=False)

    @classmethod
    def poll(cls,context):
        return (context.active_pose_bone and context.mode=='POSE') or (context.active_object and context.mode != 'POSE')
        
    def create_tracking_points(self,tracking_infos,target_name,settings):
        
        prefs = bpy.context.preferences.addons[MotionTrailPreferences.bl_idname].preferences

        # x (1.000000, 0.032185, 0.000000), 1.000000)
        color_mag = .8
        post_color_mag = .5
        active_color_mag = 1
        magnitude = 1 
        tracking_info = tracking_infos.add()
        tracking_info.name = 'right'
        tracking_info.set_location((magnitude,0,0))
        tracking_info.ptsize_tracking = prefs.ptsize_tracking
        tracking_info.ptcolor_tracking_prior =  (0.916345, 0.936860, 1.000000)
        tracking_info.ptcolor_tracking_post =  (0.916345, 0.936860, 1.000000)
        tracking_info.lcolor_tracking_prior = (1.000000, 0.032185, 0.000000)
        tracking_info.lcolor_tracking_post  = (0.290109, 0.000000, 0.000000)
        tracking_info.color_tracking_active = (1.000000, 0.032185, 0.000000)#(active_color_mag,0,0)
        tracking_info.lsize_tracking = prefs.lsize_tracking
        tracking_info.show_continuous=False
        tracking_info.show_lines_from_target=True 
        
        result = [tracking_info]
        
        tracking_info = tracking_infos.add()
        tracking_info.name = 'up'
        tracking_info.set_location((0,magnitude,0))
        tracking_info.ptsize_tracking = prefs.ptsize_tracking
        tracking_info.ptcolor_tracking_prior =  (0.916345, 0.936860, 1.000000)
        tracking_info.ptcolor_tracking_post =  (0.916345, 0.936860, 1.000000)
        tracking_info.lcolor_tracking_prior = (0.012556, 10.378156, 0.086338)
        tracking_info.lcolor_tracking_post  =(0.069223, 0.413166, 0.056837)
        tracking_info.color_tracking_active = (0.012556, 10.378156, 0.086338)
        tracking_info.lsize_tracking = prefs.lsize_tracking
        tracking_info.show_continuous=False
        tracking_info.show_lines_from_target=True 

        result.append(tracking_info)
        
        tracking_info = tracking_infos.add()
        tracking_info.name = 'forward'
        tracking_info.set_location((0,0,magnitude))
        tracking_info.ptsize_tracking = prefs.ptsize_tracking
        tracking_info.ptcolor_tracking_prior =  (0.916345, 0.936860, 1.000000)
        tracking_info.ptcolor_tracking_post =  (0.916345, 0.936860, 1.000000)
        tracking_info.lcolor_tracking_prior =  (0.000000, 0.559135, 8.955208)
        tracking_info.lcolor_tracking_post  =(0.000000, 0.000000, 0.254622)
        tracking_info.color_tracking_active = (0.000000, 0.559135, 8.955208)
        tracking_info.lsize_tracking = prefs.lsize_tracking
        tracking_info.show_continuous=False
        tracking_info.show_lines_from_target=True 

        result.append(tracking_info)
        return result

    def execute(self, context):
        settings = context.scene.motion_trail3D_settings
        
        if self.is_bone and context.mode == 'POSE':
            tracking_infos = context.active_pose_bone.motion_trail3D.tracking_points
            target_name = context.active_pose_bone.name 
            result = self.create_tracking_points(tracking_infos,target_name,settings)

            for tracking_info in result:
                tracking_info.set_length(context.active_pose_bone.length)
            #for pose_bone in context.selected_pose_bones:
            #    tracking_infos =pose_bone.motion_trail3D.tracking_points
            #    target_name = pose_bone.name 
            #    self.create_tracking_points(tracking_infos,target_name,settings)
        else:
            tracking_infos = context.active_object.motion_trail3D.tracking_points
            target_name = context.active_object.name 
            result = self.create_tracking_points(tracking_infos,target_name,settings)
    
            #for obj in context.selected_objects:
            #    tracking_infos = context.active_object.motion_trail3D.tracking_points
            #    target_name = context.active_object.name 
            #    self.create_tracking_points(tracking_infos,target_name,settings)
                
        
        context.scene.frame_set(context.scene.frame_current)#redraw..
        return {'FINISHED'}

class POSE_OT_AddTrackingPoint(bpy.types.Operator):
    '''Add tracking point'''
    bl_idname = "pose.custom_motion_trail_add_tracking_point"
    bl_label = "Add Tracking Point"
    bl_options = {'REGISTER', 'UNDO'}

    is_bone :BoolProperty('Is Bone',default=False)
    @classmethod
    def poll(cls,context):
        return ((context.active_pose_bone and context.mode=='POSE') or (context.active_object and context.mode != 'POSE'))
        
    def execute(self, context):
        settings = context.scene.motion_trail3D_settings
        prefs = context.preferences.addons[MotionTrailPreferences.bl_idname].preferences


        cursor_location = context.scene.cursor.location

        if self.is_bone and context.mode == 'POSE':
            tracking_infos = context.active_pose_bone.motion_trail3D.tracking_points
            target_name = context.active_pose_bone.name

            #could've used target.matrix_world if obj, or self.active_object.matrix_world @ self.target.matrix if bone.
            world_from_target = context.active_object.matrix_world @ context.active_pose_bone.matrix 
            target_from_cursor = (world_from_target.inverted() @ Matrix.Translation(Vector(cursor_location))).to_translation()
            
            tracking_info = tracking_infos.add()
            tracking_info.set_location(target_from_cursor)
            tracking_info.name = 'tracker_point'
            tracking_info.ptsize_tracking = prefs.ptsize_tracking
            tracking_info.ptcolor_tracking_prior = prefs.ptcolor_tracking_prior
            tracking_info.ptcolor_tracking_post = prefs.ptcolor_tracking_post
            tracking_info.lcolor_tracking_prior = prefs.lcolor_tracking_prior
            tracking_info.lcolor_tracking_post = prefs.lcolor_tracking_post
            tracking_info.color_tracking_active = prefs.color_tracking_active
            tracking_info.lsize_tracking = prefs.lsize_tracking

           
        else:
            tracking_infos = context.active_object.motion_trail3D.tracking_points
            target_name = context.active_object.name
            
            #could've used target.matrix_world if obj, or self.active_object.matrix_world * self.target.matrix if bone.
            world_from_target = context.active_object.matrix_world
            target_from_cursor = (world_from_target.inverted() @ Matrix.Translation(Vector(cursor_location))).to_translation()
            
            tracking_info = tracking_infos.add()
            tracking_info.set_location(target_from_cursor)
            tracking_info.name = 'tracker_point'
            tracking_info.ptsize_tracking = prefs.ptsize_tracking
            tracking_info.ptcolor_tracking_prior = prefs.ptcolor_tracking_prior
            tracking_info.ptcolor_tracking_post = prefs.ptcolor_tracking_post
            tracking_info.lcolor_tracking_prior = prefs.lcolor_tracking_prior
            tracking_info.lcolor_tracking_post = prefs.lcolor_tracking_post
            tracking_info.color_tracking_active = prefs.color_tracking_active
            tracking_info.lsize_tracking = prefs.lsize_tracking
        
        context.scene.frame_set(context.scene.frame_current)#redraw..
        return {'FINISHED'}
class POSE_OT_ResetTrackingPoint(bpy.types.Operator):
    '''Reset tracking point'''
    bl_idname = "pose.custom_motion_trail_reset_tracking_point"
    bl_label = "Reset Tracking Point"
    bl_options = {'REGISTER', 'UNDO'}

    index : IntProperty(name='Tracking Point Index')
    is_bone :BoolProperty('Is Bone',default=False)
    @classmethod
    def poll(cls,context):
        return ((context.active_pose_bone and context.mode=='POSE') or (context.active_object and context.mode != 'POSE'))
        
    def execute(self, context):
        
        cursor_location = context.scene.cursor.location

        if self.is_bone and context.mode == 'POSE':
            tracking_infos = context.active_pose_bone.motion_trail3D.tracking_points

            #could've used target.matrix_world if obj, or self.active_object.matrix_world @ self.target.matrix if bone.
            world_from_target = context.active_object.matrix_world @ context.active_pose_bone.matrix 
            target_from_cursor = (world_from_target.inverted() @ Matrix.Translation(Vector(cursor_location))).to_translation()
            
            tracking_infos[self.index].set_location(target_from_cursor)
        else:
            tracking_infos = context.active_object.motion_trail3D.tracking_points
            
            #could've used target.matrix_world if obj, or self.active_object.matrix_world @ self.target.matrix if bone.
            world_from_target = context.active_object.matrix_world
            target_from_cursor = (world_from_target.inverted() @ Matrix.Translation(Vector(cursor_location))).to_translation()
            
            tracking_infos[self.index].set_location(target_from_cursor)
        
        context.scene.frame_set(context.scene.frame_current)#redraw..
        return {'FINISHED'}
class POSE_OT_ClearTrackingPoint(bpy.types.Operator):
    '''Clear tracking point'''
    bl_idname = "pose.custom_motion_trail_clear_tracking_point"
    bl_label = "Clear Tracking Point"
    bl_options = {'REGISTER', 'UNDO'}

    index : IntProperty(name='Tracking Point Index')
    is_bone :BoolProperty('Is Bone',default=False)

    @classmethod
    def poll(cls,context):
        return (context.active_pose_bone and context.mode=='POSE') or (context.active_object and context.mode != 'POSE')
        
    def execute(self, context):
        
        tracking_infos = context.active_object.motion_trail3D.tracking_points
        if self.is_bone and context.mode == 'POSE':
            tracking_infos = context.active_pose_bone.motion_trail3D.tracking_points
            
        tracking_infos.remove(self.index)

        context.scene.frame_set(context.scene.frame_current)#redraw..
        return {'FINISHED'}
class POSE_OT_ClearTrackingPoints(bpy.types.Operator):
    '''Clear tracking points'''
    bl_idname = "pose.custom_motion_trail_clear_tracking_points"
    bl_label = "Clear Tracking Points"
    bl_options = {'REGISTER', 'UNDO'}

    is_bone :BoolProperty('Is Bone',default=False)

    @classmethod
    def poll(cls,context):
        return (context.active_pose_bone and context.mode=='POSE') or (context.active_object and context.mode != 'POSE')
        
    def execute(self, context):
        
        if self.is_bone and context.mode == 'POSE':
            context.active_pose_bone.motion_trail3D.tracking_points.clear()
        else:
            context.active_object.motion_trail3D.tracking_points.clear()

        context.scene.frame_set(context.scene.frame_current)#redraw..
        return {'FINISHED'}
class POSE_OT_MeshFromTrackingPoint(bpy.types.Operator):
    bl_idname = "pose.custom_motion_trail_mesh_from_tracking_point"
    bl_label = "Mesh From Tracking Point"
    bl_options = {'REGISTER', 'UNDO'}

    index : IntProperty(name='Tracking Point Index')
    is_bone :BoolProperty('Is Bone',default=False)

    @classmethod
    def poll(cls,context):
        return (context.active_pose_bone and context.mode=='POSE') or (context.active_object and context.mode != 'POSE')
        
    def execute(self, context):
        cached_frame = context.scene.frame_current 
        scene = context.scene 

        vertices_per_item = None 
        selected_items = None

        if self.is_bone and context.mode == 'POSE':
            tracking_infos = context.active_pose_bone.motion_trail3D.tracking_points
            obj_matrix = context.active_object.matrix_world 
            selected_items = [tracking_infos[self.index]]
            
            bone = context.active_pose_bone
            vertices_per_item = [[] for _ in selected_items]
            for i in range(scene.frame_preview_start,scene.frame_preview_end+1):
                scene.frame_set(i) 
                
                for index,info in enumerate(selected_items):
                    vertices_per_item[index].append(obj_matrix @  bone.matrix @ info.get_location())
        else:
            
            tracking_infos = context.active_object.motion_trail3D.tracking_points
            selected_items = [tracking_infos[self.index]]
            vertices_per_item = [[] for _ in selected_items]
            for i in range(scene.frame_preview_start,scene.frame_preview_end+1):
                scene.frame_set(i) 
                
                for index,info in enumerate(selected_items):
                    vertices_per_item[index].append(context.active_object.matrix_world @ info.get_location())
            
        len_verts = scene.frame_preview_end+1 - scene.frame_preview_start
        edges = [(i,i+1) for i in range(0,len_verts-1)]
        for index,item in enumerate(selected_items):
            obj = create_mesh(object_name=item.name,mesh_name=item.name)
            mesh = obj.data 
            mesh.from_pydata(vertices_per_item[index],edges,[])

        context.scene.frame_set(cached_frame)

        return {'FINISHED'}
class POSE_OT_MeshFromTrackingPoints(bpy.types.Operator):
    bl_idname = "pose.custom_motion_trail_mesh_from_tracking_points"
    bl_label = "Mesh From Tracking Points"
    bl_options = {'REGISTER', 'UNDO'}

    is_bone :BoolProperty('Is Bone',default=False)

    @classmethod
    def poll(cls,context):
        return (context.active_pose_bone and context.mode=='POSE') or (context.active_object and context.mode != 'POSE')
        
    def execute(self, context):
        cached_frame = context.scene.frame_current 
        scene = context.scene 

        vertices_per_item = None 
        selected_items = None

        if self.is_bone and context.mode == 'POSE':
            tracking_infos = context.active_pose_bone.motion_trail3D.tracking_points
            obj_matrix = context.active_object.matrix_world 
            selected_items = [info for info in tracking_infos if info.show_tracking]
            
            bone = context.active_pose_bone
            vertices_per_item = [[] for _ in selected_items]
            for i in range(scene.frame_preview_start,scene.frame_preview_end+1):
                scene.frame_set(i) 
                
                for index,info in enumerate(selected_items):
                    vertices_per_item[index].append(obj_matrix @ bone.matrix @ info.get_location())
        else:
            
            tracking_infos = context.active_object.motion_trail3D.tracking_points
            selected_items = [info for info in tracking_infos if info.show_tracking]
            vertices_per_item = [[] for _ in selected_items]
            for i in range(scene.frame_preview_start,scene.frame_preview_end+1):
                scene.frame_set(i) 
                
                for index,info in enumerate(selected_items):
                    vertices_per_item[index].append(context.active_object.matrix_world @ info.get_location())

        len_verts = scene.frame_preview_end+1 - scene.frame_preview_start
        edges = [(i,i+1) for i in range(0,len_verts-1)]
        #faces = [(i,i+1,len_verts) for i in range(0,len_verts-1)]
        
        for index,item in enumerate(selected_items):
            obj = create_mesh(object_name=item.name,mesh_name=item.name)
            mesh = obj.data 
            mesh.from_pydata(vertices_per_item[index],edges,[])

        context.scene.frame_set(cached_frame)

        return {'FINISHED'}


class POSE_OT_PathToMesh(bpy.types.Operator):
    '''Generate mesh from path'''
    bl_idname = "pose.path_to_mesh"
    bl_label = "Path To Mesh"
    bl_options = {'REGISTER', 'UNDO'}

    head_to_tail : FloatProperty(name='Head Tail',default=0,soft_min=0,soft_max=1)
    @classmethod
    def poll(cls,context):
         return (context.active_pose_bone and context.mode=='POSE') or (context.active_object and context.mode == 'OBJECT')

    def invoke(self, context, event):
        if context.mode == 'POSE':
            wm = context.window_manager
            return wm.invoke_props_dialog(self)
        
        return self.execute(context) 


    def execute(self, context):
        cached_frame = context.scene.frame_current 
        scene = context.scene

        vertices_per_item = None 
        selected_items = []
        #reason we dont just do both bones and objects at same time is due to obj selection possibly including armature when pose bone selected
        if context.mode=='POSE':
            obj_matrix = context.active_object.matrix_world 
            head = Vector((0,0,0))
            mu = self.head_to_tail 
            
            selected_items = context.selected_pose_bones[:]

            vertices_per_item = [[] for _ in selected_items]
            for i in range(scene.frame_preview_start,scene.frame_preview_end+1):
                scene.frame_set(i) 
                
                for index,bone in enumerate(selected_items):
                    tail = Vector((0,bone.length,0))
                    head_tail = ((1-mu) * head) + (mu * tail) 

                    vertices_per_item[index].append((obj_matrix @ bone.matrix @ head_tail))
        else:
            
            selected_items = context.selected_objects[:]

            vertices_per_item = [[] for _ in selected_items]
            for i in range(scene.frame_preview_start,scene.frame_preview_end+1):
                scene.frame_set(i) 
                
                for index,obj in enumerate(selected_items):
                    vertices_per_item[index].append(obj.matrix_world.to_translation())
            
        len_verts = scene.frame_preview_end+1 - scene.frame_preview_start
        edges = [(i,i+1) for i in range(0,len_verts-1)]
        for index,item in enumerate(selected_items):
            obj = create_mesh(object_name='path_'+item.name,mesh_name='path_'+item.name)
            mesh = obj.data 
            mesh.from_pydata(vertices_per_item[index],edges,[])

        context.scene.frame_set(cached_frame)

        return {'FINISHED'}

class POSE_OT_MotionTrailBeginTag(bpy.types.Operator):
    bl_idname = "pose.motion_trail_begin_tag"
    bl_label = "** BEGIN Motion Trail **"
    #bugfix: do not use 'REGISTER', changing timeline range using redo panel results in bugs on next trail activate. 
    #such support isn't recommended anyways. Why start a trail just to change its preview range immediately afterwards.
    bl_options = { 'UNDO'}

    frame_preview_start  : IntProperty(name='Frame Preview Start',default=0)
    frame_preview_end : IntProperty(name='Frame Preview End', default = 30)

    @classmethod
    def poll(cls,context):
        settings = context.scene.motion_trail3D_settings
        
        target_object = (context.mode == 'OBJECT') and context.active_object
        target_pose_bone = (context.mode == 'POSE') and context.active_pose_bone

        return  (target_object or target_pose_bone) #and   (not settings.is_active)



    def invoke(self, context, event):

        if not context.scene.use_preview_range:
            wm = context.window_manager
            
            self.frame_preview_start,self.frame_preview_end = context.scene.frame_preview_start,context.scene.frame_preview_end 
            return wm.invoke_props_dialog(self)
        else:
            self.frame_preview_start,self.frame_preview_end = context.scene.frame_preview_start,context.scene.frame_preview_end 
            return self.execute(context)

    def execute(self, context):
        
        context = ContextOverride(context) 
        if context.mode =='POSE':

            added = False 
            for target in context.selected_pose_bones:
                
                _,trail_exists = get_registered_trailOp(target.name) 
                if not trail_exists:
                    added= True
                    context.active_pose_bone = target 
                    #in case in multi-object pose mode 
                    context.active_object = target.id_data 
                    self.invoke_trail(context)
                    print_time('trail activated for bone: ' + target.name)

            if added:
                #adds all new trails to global draw callback
                reorder_trail_updates()
                #forces a scene_update() incase it hasn't happened yet. unsure why it rarely isn't called. Should fix it.
                bpy.ops.object.mode_set(mode='POSE')
        else:
            added = False 
            for target in context.selected_objects:
                
                _,trail_exists = get_registered_trailOp(target.name)
                if not trail_exists:
                    added= True
                    context.active_pose_bone = None  
                    #in case in multi-object pose mode 
                    context.active_object = target 
                    self.invoke_trail(context)
                    print_time('trail activated for object: ' + target.name)
            if added:
                #adds all new trails to global draw callback
                reorder_trail_updates()
                #forces a scene_update() incase it hasn't happened yet. unsure why it rarely isn't called. Should fix it.
                bpy.ops.object.mode_set(mode='OBJECT')
        return {'FINISHED'}
                
    def invoke_trail(self,context):
        #todo: if obj mode, go through all selected objects and call trail op on them.... but trail op itself looks for the target... so will need to either override context or set prop between op calls
        #convenience: default to creating action if it doesn't exist
        animation_data = context.active_object.animation_data
        if not animation_data:
            animation_data = context.active_object.animation_data_create()
        if not animation_data.action:
            animation_data.action = bpy.data.actions.new('Action')
            
        settings = context.scene.motion_trail3D_settings
        #settings.render_trail=True
        context.scene.use_preview_range= True 
        context.scene.frame_preview_start,context.scene.frame_preview_end = self.frame_preview_start,self.frame_preview_end

        #print('starting trail')
        #this inserts an undo tag at the start of the motion trail so users can see how far to undo.
        bpy.ops.pose.custom_motion_trail_end_tag('INVOKE_DEFAULT')
        

class POSE_OT_DeactivateAll(bpy.types.Operator):
    '''This should only be used in the case where no trail is active but you're unable to start a new one'''
    bl_idname = "pose.motion_trail_deactivate_all"
    bl_label = "*Trail Deactivate All"
    bl_options = {'REGISTER', 'UNDO'}

    @classmethod
    def poll(cls,context):
        return len(context.scene.motion_trail3D_settings.active_trails) > 0 

    def execute(self, context):

        #leads to all active trails disposing themselves
        for trail in reversed(context.scene.motion_trail3D_settings.active_trails):
            unregister_trailOp(trail.target_name)
            #context.scene.motion_trail3D_settings.active_trails.clear() 
            
        return {'FINISHED'}
class POSE_OT_Deactivate(bpy.types.Operator):
    '''This should only be used in the case where no trail is active but you're unable to start a new one'''
    bl_idname = "pose.motion_trail_deactivate"
    bl_label = "*Deactivate Trail"
    bl_options = {'REGISTER', 'UNDO'}


    target_name :StringProperty(default='',name='Target Name')
    @classmethod
    def poll(cls,context):
        return len(context.scene.motion_trail3D_settings.active_trails) > 0 

    def execute(self, context):


        if len(self.target_name) > 0:
            unregister_trailOp(self.target_name)

        return {'FINISHED'}
class POSE_OT_CustomMotionTrail(bpy.types.Operator):
    bl_idname = "pose.custom_motion_trail_end_tag"
    bl_label = "** END Motion Trail **"
    bl_options = {'UNDO'}

    def reset_instance_fields(self):        
        #by calling this on invoke and dispose, ensure trail re-activation doesn't error due to data from  last use.
        #redundant double call by dispose to get rid of unnecessary data tracked by Blender
        #self.apples = 0.0
        #self.debug_test = 1
        #self.debug_just_snapped=False
        #self.debug_counter = 0


        self.total_timers = 0
        self.show_time = False
        self.show_co = False
        self.show_handles = False
        self.show_hidden_time = False
        self.show_hidden_co = False
        self.show_hidden_handles = False
        self.controller_scale = 1

        self.ptr_active_object = None 
        self.active_object = None

        self.updated_active_object=False
        #avoid circular updates when we sync fcruve data to object data
        #if ignore(True), then only allowed items can update
        #if ignore(False), then all items allowed to update regardless of items in it.
        self.ignore_control_update_once=True
        self.allowed_control_update = set()
        #used to sync ctrls from channels after ctrls done being dragged by user 
        #self.ctrl_was_moved=False

        #used to prevent infinite loops.
        #Updating objects within scene_update doesn't cause infinite loop
        #Updating obj within draw() will cause a scene_update() which causes another draw().
        #Updating an obj outside of scene_update() will cause another scene_update():
        #   -so we use the flag on the snap timer call.
        #   -but there is never a need to set the flag while in scene_update
        #   -(guess)in fact, it may cause an initial modal op start apparent delay if flag left set to true after a scene_update.
        self.ignore_time_sync_once=False
        self.time_objects_was_changed = False
        #self.steps_since_objects_was_changed = 0
        #tmp_control_update_info_type = []
        #tmp_control_update_info_key_index = []
        self.ERROR_motion_trail = False
        #used as a hack to check when operator finished, in order to snap objects less frequently while animation playing to making snapping less annoying.
        self.pre_op_history_len =0
        
        self.prev_trail_mode = 'LOCATION'
        self.prev_rotation_mode = 'XYZ'
        self.active_trail_data = None
        self.prev_trail_data = None 


        #self.cached_len_xKeys =0
        #self.cached_len_yKeys =0
        #self.cached_len_zKeys =0

        self.buffered_framed_set = None
        #in 2.79, change to total tracker points is handled by update handler
        #in 2.80, adding tracker points does
        #self.total_tracker_points = 0

        self.profiler_items = []
        self.parent_calls = [] 


        self.prev_relative_parent_object = "" 
        self.prev_relative_parent_bone = ""
        self.prev_relative_parent_frame = -1
        self.prev_enable_relative_parent = False
        self.relative_parent_is_valid=False 

        self.prev_dependency_target = "" 
        self.prev_dependency_active = False 
        self.prev_dependency_inherit_loc = False 
        self.prev_dependency_inherit_rot = False 
        self.prev_dependency_inherit_scale = False 
        self.prev_dependency_keep_self_rot = False 
        self.dependency_target_is_valid = False 


        self.prev_control_offset_name = ""
        self.prev_control_offset_vector = Vector()
        if profile:
            wrapped,parent_calls = profile_wrap_functions(self, {'init_motion_trail','calculate_parent_matrix_cache'},{'scene_update','draw_callback_px','trail_update'})
            self.profiler_items.extend(wrapped)
            self.parent_calls.extend(parent_calls)
        if debug_crash_search:
            debug_wrap_func_exec(self,{})


    def get_control_offset_matrix(self):
        return Matrix.Translation(self.get_control_offset_vector())

    def get_control_offset_vector(self):
        control_offset = Vector()
        trailOp = self.get_trail_info()
        if len(trailOp.control_offset_tracker_name) > 0:
            tracking_points = self.target.motion_trail3D.tracking_points 
            for tracker in tracking_points:
                if tracker.name == trailOp.control_offset_tracker_name:
                    control_offset = tracker.get_location()
        return control_offset
    
    def debug_crash_check_check_control_offset_change(self):
        trailOp = self.get_trail_info()
        current_location = self.get_control_offset_vector() 

        tracker_changed = self.prev_control_offset_name != trailOp.control_offset_tracker_name
        loc_changed = (current_location - self.prev_control_offset_vector).magnitude > .001 

        if tracker_changed or loc_changed:
            self.debug_delete_all_objects()

    def check_control_offset_change(self):
        trailOp = self.get_trail_info()
        current_location = self.get_control_offset_vector() 

        tracker_changed = self.prev_control_offset_name != trailOp.control_offset_tracker_name
        loc_changed = (current_location - self.prev_control_offset_vector).magnitude > .001 

        if tracker_changed or loc_changed:
            #print_time('lets see')
            self.prev_control_offset_name = trailOp.control_offset_tracker_name
            self.prev_control_offset_vector = current_location 

            #write to hidden controls
            self.allowed_control_update.clear()
            self.active_trail_data.clear_updated()
            self.calculate_control_worlds() 
            self.sync_time_ctrl_locations()
            return True 
        return False 
    def calculate_world_from_dependency_matrix(self,info,nonrel_matrix,dep_matrix,target_matrix,debug_print=False):
        
        result = target_matrix @ dep_matrix 
        if info.is_inherit_FULL():  
            return result 
        else:
            resloc,resrot,resscale = result.decompose()
            defloc,defrot,defscale = nonrel_matrix.decompose()
            tloc,trot,tscale = target_matrix.decompose()
            #initial target from which dep/relative matrix calculated from
            tiloc,tirot,tiscale = (dep_matrix @ nonrel_matrix.inverted()).inverted().decompose()


            #location calcs
            if info.inherit_loc == 'FULL':
                pass 
            elif info.inherit_loc == 'NONE':
                #use nonrel to get nonxformed/nonrel world
                resloc = defloc
            elif info.inherit_loc == 'LOC':
                #if debug_print:
                #    print()
                #    print("tirot:{}\ntrot:{}".format(tirot,trot))
                #    print("tiloc:{}\ntloc:{}".format(tiloc,tloc))
                tmp = matrix_trs(tloc,tirot,tiscale)
                resloc = (tmp @ dep_matrix).decompose()[0]
            elif info.inherit_loc == 'LOCROT':
                tmp = matrix_trs(tloc,trot,tiscale)
                resloc = (tmp @ dep_matrix).decompose()[0]
            elif info.inherit_loc =='LOCSCALE':
                tmp = matrix_trs(tloc,tirot,tscale)
                resloc = (tmp @ dep_matrix).decompose()[0]
            
            #rotation
            if not info.inherit_rot:
                resrot = defrot
            #scale
            if not info.inherit_scale:
                resscale = defscale
            
            result = matrix_trs(resloc,resrot,resscale)
            return result 
    def debug_crash_check_apply_trail_dependency_flags_change(self,force_recalc=False):
        #WARNING: do not place in draw_callback_px()  since frame_sets() will cause infinite recursion
    
        print_conditional(debug_enable_print_func_tags,'')
        settings = bpy.context.scene.motion_trail3D_settings
        info = self.get_trail_info().dependency
        current_frame = bpy.context.scene.frame_current
        frame_start,frame_end = self.frame_start,self.frame_end 
        frames_length  = frame_end-frame_start + 1
        enable_change = info.is_active != self.prev_dependency_active
        info_changed = (info.target_name != self.prev_dependency_target)  or \
            (info.inherit_loc != self.prev_dependency_inherit_loc) or \
            (info.inherit_rot != self.prev_dependency_inherit_rot) or \
            (info.inherit_scale != self.prev_dependency_inherit_scale) #or \
            #(info.keep_self_rot != self.prev_dependency_keep_self_rot) 

        #only do recalc if enable-change or was enabled and other props changed
        #basically, avoid recalc if disabled and parent info changed
        if enable_change or (info.is_active and info_changed) or force_recalc:
            self.debug_delete_all_objects()
    
    def apply_trail_dependency_flags_change(self,force_recalc=False):
        
        print_conditional(debug_enable_print_func_tags ,'apply_trail_dependency_flags_change...')
        #WARNING: do not place in draw_callback_px()  since frame_sets() will cause infinite recursion
        
        print_conditional(debug_enable_print_func_tags,'')
        settings = bpy.context.scene.motion_trail3D_settings
        info = self.get_trail_info().dependency
        current_frame = bpy.context.scene.frame_current
        frame_start,frame_end = self.frame_start,self.frame_end 
        frames_length  = frame_end-frame_start + 1
        enable_change = info.is_active != self.prev_dependency_active
        info_changed = (info.target_name != self.prev_dependency_target)  or \
            (info.inherit_loc != self.prev_dependency_inherit_loc) or \
            (info.inherit_rot != self.prev_dependency_inherit_rot) or \
            (info.inherit_scale != self.prev_dependency_inherit_scale) #or \
            #(info.keep_self_rot != self.prev_dependency_keep_self_rot) 

        #only do recalc if enable-change or was enabled and other props changed
        #basically, avoid recalc if disabled and parent info changed
        if enable_change or (info.is_active and info_changed) or force_recalc:
            reorder_trail_updates()

            self.prev_dependency_target = info.target_name
            self.prev_dependency_active = info.is_active
            self.prev_dependency_inherit_loc = info.inherit_loc
            self.prev_dependency_inherit_rot = info.inherit_rot
            self.prev_dependency_inherit_scale = info.inherit_scale
            #self.prev_dependency_keep_self_rot = info.keep_self_rot
            self.dependency_target_is_valid = False 

            
            #recalc nonrelative cache since it may have been changed since trail activated, due to dep. parenting
            self.calculate_parent_matrix_cache()
            for i in range(0,frames_length):
                #note if dep. not active, then dep cache is garbage and shouldnt be used, values not useful in any context.
                self.dependency_matrix_cache[i] = Matrix.Identity(4)
                #default when dep. not active
                self.active_parent_matrix_cache[i] = self.relative_parent_inverse_matrix_cache[i] @ self.nonrelative_parent_matrix_cache[i]
                 
            

            valid_dependency_targets = {trail.target_name:trail for trail in settings.active_trails}
            if info.is_active:
                if info.target_name in valid_dependency_targets:
                    self.dependency_target_is_valid = True 
                    target_trail = valid_dependency_targets[info.target_name]
                    target_matrices = target_trail.child_dependency_matrices
                    
                    for i in range(0,frames_length):
                        #todo: support for different inheritance parms
                        #extract offset matrix from target, to be applied after every change to the most recent target matrices afterward
                        #self.dependency_matrix_cache[i] = target_matrices[i].get().inverted() @ self.nonrelative_parent_matrix_cache[i]
                        self.dependency_matrix_cache[i] =  target_matrices[i].get().inverted() @ self.nonrelative_parent_matrix_cache[i]
                        ##########self.nonrelative_parent_matrix_cache[i] = target_matrices[i].get() @ self.dependency_matrix_cache[i]
                        #placed here so rel. parent taken into account on dep. enable

                        world_from_local = self.calculate_world_from_dependency_matrix(info,self.nonrelative_parent_matrix_cache[i],self.dependency_matrix_cache[i],target_matrices[i].get())
                        self.active_parent_matrix_cache[i] = self.relative_parent_inverse_matrix_cache[i] @  world_from_local
          
            for i in range(0,frames_length):
                self.parent_positions[i] = self.active_parent_matrix_cache[i].to_translation()

            #rest of code is unnecessary if inheritance parms accurate
            #but in the case where it isnt, this will cause a visual update for verification
            #self.recalculate_triple_buffer(settings,force_relink=True) 
            self.calculate_control_worlds()
            self.ignore_control_update_once=True
            self.read_sample_points()
            self.sync_time_ctrl_locations() 

            active_trail_data = self.active_trail_data
            active_trail_data.updated_objects.clear()
            active_trail_data.updated_time_objects.clear()
            active_trail_data.prev_updated_time_objects.clear()
            self.report({'INFO'},'[{0}] Trail Dependency flag change processed..'.format( self.target_name))
            print_conditional(debug_enable_print_func_tags ,'..end apply_trail_dependency_flags_change1')
            return True
        print_conditional(debug_enable_print_func_tags ,'..end apply_trail_dependency_flags_change')
        return False 
    def apply_trail_dependency_due_parent_xformed(self):
        print_conditional(debug_enable_print_func_tags ,'apply_trail_dependency_due_parent_xformed ..')
        #WARNING: do not place in draw_callback_px()  since frame_sets() will cause infinite recursion
        
        settings = bpy.context.scene.motion_trail3D_settings
        trailOp = self.get_trail_info()
        info = trailOp.dependency
        frame_start,frame_end = self.frame_start,self.frame_end 
        frames_length  = frame_end-frame_start + 1
        
        info_changed = (info.target_name != self.prev_dependency_target)  or \
            (info.inherit_loc != self.prev_dependency_inherit_loc) or \
            (info.inherit_rot != self.prev_dependency_inherit_rot) or \
            (info.inherit_scale != self.prev_dependency_inherit_scale)# or \
            #(info.keep_self_rot != self.prev_dependency_keep_self_rot) 

        parent_trailOp = self.dependency_trailOp_get()
        
        #only do recalc if enable-change or was enabled and other props changed
        #basically, avoid recalc if disabled and parent info changed
        #without the check on parent.has_updated, then ignore will always be true thus not allowing ctrl to be dragged.
        
        if (not info_changed) and info.is_active and (parent_trailOp and trailOp.hierarchy_has_updated):
            valid_dependency_targets = {trail.target_name:trail for trail in settings.active_trails}
            if info.is_active:
                
                if info.target_name in valid_dependency_targets:
                    target_trail = valid_dependency_targets[info.target_name]
                    target_matrices = target_trail.child_dependency_matrices
                        
                        
                    for i in range(0,frames_length):
                        #todo: support for different inheritance parms\
                        #todo: non rel cache would also be affected by inehritance flags
                        #active cache set such that all sample pts and ctrls are relative to the relative_parent at the current frame.
                        #self.nonrelative_parent_matrix_cache[i] = target_matrices[i].get() @ self.dependency_matrix_cache[i]

                        world_from_local = self.calculate_world_from_dependency_matrix(info,self.nonrelative_parent_matrix_cache[i],self.dependency_matrix_cache[i],target_matrices[i].get(),debug_print=i==0)

                        self.nonrelative_parent_matrix_cache[i] = world_from_local 
                        #since nonrelative was updated, need to update the offset from the target since calc_world_from.. uses both
                        self.dependency_matrix_cache[i] =  target_matrices[i].get().inverted() @ world_from_local
                        self.active_parent_matrix_cache[i] = self.relative_parent_inverse_matrix_cache[i] @  world_from_local
                        #self.active_parent_matrix_cache[i] = self.relative_parent_inverse_matrix_cache[i] @ target_matrices[i].get() @ self.dependency_matrix_cache[i]
                            
                    for i in range(0,frames_length):
                        self.parent_positions[i] = self.active_parent_matrix_cache[i].to_translation()
                        
                    #todo:consider instead of reading controls, may need to write world ctrl values?
                    #because if parent moved, then local has changed relative to parent?..no because parent moves child and therefore even local is const. what if not the general case?

                    #todo: bug: currently, cant modfiy trail target when dependency active due to these lines overwriting world
                    #so maybe need a flag for dep. to set when its being xformed.
                    #and if so, ? do nothing till its done becauase maybe parent and child are dxforemd too? then what happens? 
                    #dont clear upated objects during this time so when flag turns off, we can go through them?
                    #the order must be: let parent update its matrices, then child can apply its changes and so on. But child must not apply its changes before the parent.
                    #but how can I enforce such update ordering? The guarantee is that the funcs are callbacks and I'm hoping the callbacks are called in order of addition. See no reason for it to be random.
                    #so maybe, on dependency enable, go through the callback list, find the parent's callback and swap if it's called after own trail?
                    #rest of code is unnecessary if inheritance parms accurate
                    #but in the case where it isnt, this will cause a visual update for verification
                    #self.recalculate_triple_buffer(settings,force_relink=True) 
                    
                    #print_time('dep. heirarchy updated: ' + self.target_name )
                    self.write_controls_to_channels()
                    self.ignore_control_update_once=True
                    self.calculate_control_worlds()
                    self.read_sample_points()
                    self.sync_time_ctrl_locations() 

                    #-so if parent updated and child not (discern by looking at obj update list? but wouldnt work for Fcurve changes to parent)
                    #then child needs world ctrls read again, to offset with parent
                    #-if both xforemed, then need to write parent first, then write child using new relative matrix cache. Don't read to child ctrl.B

                    #consider:what if I only read to non-selected ctrls, write selected ctrls? 
                    #then if only parent xformed, then ctrl moves with parent
                    #if both xformed, then ctrl will write (after cache updated)
                    #active_trail_data = self.active_trail_data
                    #updated_objects = active_trail_data.updated_objects
                    #updated_time_objects = active_trail_data.updated_time_objects
        print_conditional(debug_enable_print_func_tags ,'..end apply_trail_dependency_due_parent_xformed')
    def current_frame_to_index(self):
        return clamp(bpy.context.scene.frame_current - self.frame_start,0,self.frame_end - self.frame_start)

    def debug_try_crash_relative_parent_check_flags_change(self):
        #this func will delete all objects at the same time parent flags change
        #if it throws an error during the core func, then we have found a bug
        #validate_objects() should've caught the missing objects.
        
        settings = bpy.context.scene.motion_trail3D_settings
        current_frame = bpy.context.scene.frame_current
        frame_start,frame_end = self.frame_start,self.frame_end 
        frames_length  = frame_end-frame_start + 1
        enable_change = settings.enable_relative_parent != self.prev_enable_relative_parent
        parent_info_changed = settings.relative_parent_object != self.prev_relative_parent_object or\
            settings.relative_parent_bone != self.prev_relative_parent_bone 

        #only do recalc if enable-change or was enabled and other props changed
        #basically, avoid recalc if disabled and parent info changed
        if enable_change or (settings.enable_relative_parent and parent_info_changed):
            self.debug_delete_all_objects()
    def debug_delete_all_objects(self):
        objects = bpy.data.objects
        
        #print('h')
        #dont deref, gotta match core func ref uses
        root = self.ptr_all_control_points_root.deref()

        #print('i')
        for obj in root.children:#
            #print('j')
            objects.remove( obj,do_unlink=True)

        #checking to ensure updated objects are validated too.
        active_trail_data = self.active_trail_data
        for control_type,objects in enumerate(active_trail_data.key_objects.grouped):
            for i,obj in enumerate(objects):
                active_trail_data.updated_objects.grouped[control_type].add(obj) 
        for control_type,objects in enumerate(active_trail_data.key_time_objects.grouped):
            for i,obj in enumerate(objects):
                active_trail_data.updated_time_objects.grouped[control_type].add(obj)

    def relative_parent_check_flags_change(self,force_recalc=False):
        print_conditional(debug_enable_print_func_tags ,'relative_parent_check_flags_change...')
        #WARNING: do not place in draw_callback_px()  since frame_sets() will cause infinite recursion
        
        settings = bpy.context.scene.motion_trail3D_settings
        current_frame = bpy.context.scene.frame_current
        frame_start,frame_end = self.frame_start,self.frame_end 
        frames_length  = frame_end-frame_start + 1
        enable_change = settings.enable_relative_parent != self.prev_enable_relative_parent
        parent_info_changed = settings.relative_parent_object != self.prev_relative_parent_object or\
            settings.relative_parent_bone != self.prev_relative_parent_bone 

        #only do recalc if enable-change or was enabled and other props changed
        #basically, avoid recalc if disabled and parent info changed
        if enable_change or (settings.enable_relative_parent and parent_info_changed) or force_recalc:
            self.prev_relative_parent_object = settings.relative_parent_object
            self.prev_relative_parent_bone = settings.relative_parent_bone  
            self.prev_frame = current_frame
            self.prev_enable_relative_parent = settings.enable_relative_parent
            self.relative_parent_is_valid=False 
            reorder_trail_updates()

            #recalc default cache in case of invalidated parent
            #call not necessary, nonrelative cache unchanged (only in case where heirarchy not xformed, but could become the general case when using dep. parenting, so we recalc it anyways)
            #print_time('pre calc matrix cache...')
            self.calculate_parent_matrix_cache()
            #print_time('.. calc matrix cache')
            for i in range(0,frames_length):
                self.relative_parent_inverse_matrix_cache[i] = Matrix.Identity(4)
                
            #todo:fix:bug: target_matrices may update at any time, so need a solution that accounts for that
            if self.dependency_target_is_valid:
                valid_dependency_targets = {trail.target_name:trail for trail in settings.active_trails}
                info = self.get_trail_info().dependency
                target_trail = valid_dependency_targets[info.target_name]
                target_matrices = target_trail.child_dependency_matrices
                for i in range(0,frames_length):
                    #active cache set such that all sample pts and ctrls are relative to the relative_parent at the current frame.
                    #since we recalced nonrel cache, need to recalc dep. cache
                    self.dependency_matrix_cache[i] = target_matrices[i].get().inverted() @ self.nonrelative_parent_matrix_cache[i]
                    #identity_matrix_cache[i] = target_matrices[i].get() @ self.dependency_matrix_cache[i]

            #print_time('A')
            #for i in range(0,frames_length):
            #    self.active_parent_matrix_cache[i] = self.nonrelative_parent_matrix_cache[i].copy()
            #    self.relative_parent_inverse_matrix_cache[i] = Matrix.Identity(4)


            relative_parent_is_self = False
            if settings.relative_parent_object in bpy.data.objects:
                parent_object = bpy.data.objects[settings.relative_parent_object]
                if isinstance(parent_object.data,bpy.types.Armature) and len(settings.relative_parent_bone) > 0:
                    if settings.relative_parent_bone == self.target_name:
                        relative_parent_is_self = True
                elif settings.relative_parent_object == self.target_name:
                    relative_parent_is_self = True 

            #print_time('B')
            #parent_matrix_cache will be modified such that it's xformed as relative to trail parent space per frame
            #active_parent_matrix_cache  applies, at the current frame, the parent matrix. 
            #therefore, rendered points using active_parent_matrix cache will be a curve that visually moves with parent
            #rendered points using nonrelative_parent_matrix cache will be in world space and const as parent moves (since there is no dependency) 
            if settings.enable_relative_parent and not relative_parent_is_self:
                if settings.relative_parent_object in bpy.data.objects:
                    parent_object = bpy.data.objects[settings.relative_parent_object]
                    if isinstance(parent_object.data,bpy.types.Armature) and len(settings.relative_parent_bone) > 0:
                        if settings.relative_parent_bone in parent_object.pose.bones:
                            
                            #print_time('C')
                            self.relative_parent_is_valid=True 
                            parent_bone = parent_object.pose.bones[settings.relative_parent_bone]
                                    
                            #here,copy not necessary, just to be clear that its const as frame changes
                            ####self.current_relative_parent_matrix = ( parent_object.matrix_world @ parent_bone.matrix).copy()
                            ####self.all_control_points_root.matrix_world = self.current_relative_parent_matrix.copy()
                                
                            #print_time('D')
                            root = self.all_control_points_root
                            #need to bake entire xform....
                            
                            root.animation_data_clear()
                            root.keyframe_insert('location',index=-1,frame=self.frame_start,group=TAG_root_action_group)
                            root.keyframe_insert('location',index=-1,frame=self.frame_end,group=TAG_root_action_group)
                            root.keyframe_insert('rotation_quaternion',index=-1,frame=self.frame_start,group=TAG_root_action_group)
                            root.keyframe_insert('rotation_quaternion',index=-1,frame=self.frame_end,group=TAG_root_action_group)
                            root.keyframe_insert('scale',index=-1,frame=self.frame_start,group=TAG_root_action_group)
                            root.keyframe_insert('scale',index=-1,frame=self.frame_end,group=TAG_root_action_group)

                            root_channels = root.animation_data.action.groups[TAG_root_action_group].channels
                            #print([f'{channel.data_path}[{channel.array_index}]' for channel in root_channels])
                            for channel in root_channels:
                                channel.convert_to_samples(self.frame_start,self.frame_end+1)
                                #print('total samples: ' +str(len(channel.sample_points)))
                            
                            #print_time('E')
                            for i in range(0,frames_length):
                                bpy.context.scene.frame_set(i + frame_start)
                                parent_matrix_world = (parent_object.matrix_world @ parent_bone.matrix)
                                inverse_matrix = parent_matrix_world.inverted() 
                                self.relative_parent_inverse_matrix_cache[i] = inverse_matrix
                                self.active_parent_matrix_cache[i] = inverse_matrix @ self.nonrelative_parent_matrix_cache[i]
                                    
                                ploc,prot,pscale = parent_matrix_world.decompose()
                                pscale = (1,1,1)
                                for axis in range(0,3):
                                    channel = root_channels[axis]
                                    co = channel.sampled_points[i].co
                                    co[1] = ploc[axis]
                                for axis in range(0,4):
                                    channel = root_channels[3 + axis]
                                    co = channel.sampled_points[i].co
                                    co[1] = prot[axis]
                                for axis in range(0,3):
                                    channel = root_channels[7 + axis]
                                    co = channel.sampled_points[i].co
                                    co[1] = pscale[axis]
                            
                            root.matrix_world = self.relative_parent_inverse_matrix_cache[self.current_frame_to_index()].inverted()
                            root.scale=(1,1,1)
                            
                            #print_time('F')
                            #print('expecting scale of 1:',repr(self.active_parent_matrix_cache[0].decompose()[2])) #True
                            #active cache set such that all sample pts and ctrls are relative to the relative_parent at the current frame.
                            #self.active_parent_matrix_cache[i] = current_parent_world @ self.parent_matrix_cache[i] 
                                

                            #####self.all_control_points_root.parent = parent_object
                            #####self.all_control_points_root.parent_bone = parent_bone.name 
                            #####self.all_control_points_root.parent_type = 'BONE' 


                            #Blender places bone children at the tail of the parent...The inverse is also relative to the orientation of the parent bone in pose space, origin at tail.
                            #so we move the root to the bone head, as expected by the rest of the code, especially for rel_par_inv_cache.
                            #self.all_control_points_root.matrix_parent_inverse = Matrix.Translation(Vector((0,-parent_bone.length,0)))#(parent_bone.bone.matrix.to_4x4()).inverted()
                            #I dont think scale fix should happen here. Maybe its like trail dep? remove out same obj scale to avoid double applying?
                            #print( matrix_trs(Vector(),Quaternion(),Vector(parent_object.scale)).inverted())
                            #scale =  matrix_trs(Vector(),Quaternion(),Vector(parent_object.scale)) 
                            #scale =  matrix_trs(Vector(),Quaternion(),Vector((1/10,1/10,1/10))) #todo:where i left off. trying to scale ctrls to avoid double scaling by armature scale
                            
                            #####self.all_control_points_root.matrix_parent_inverse =  Matrix.Translation(Vector((0,-parent_bone.length,0))) #@ scale##(parent_bone.bone.matrix.to_4x4()).inverted()


                            bpy.context.scene.frame_set(current_frame)

                    else:

                    
                        #print_time('G')
                        root = self.all_control_points_root
                        #need to bake entire xform....
                        
                        root.animation_data_clear()
                        root.keyframe_insert('location',index=-1,frame=self.frame_start,group="__gen_motiontrail3d__")
                        root.keyframe_insert('location',index=-1,frame=self.frame_end,group="__gen_motiontrail3d__")
                        root.keyframe_insert('rotation_quaternion',index=-1,frame=self.frame_start,group="__gen_motiontrail3d__")
                        root.keyframe_insert('rotation_quaternion',index=-1,frame=self.frame_end,group="__gen_motiontrail3d__")
                        root.keyframe_insert('scale',index=-1,frame=self.frame_start,group="__gen_motiontrail3d__")
                        root.keyframe_insert('scale',index=-1,frame=self.frame_end,group="__gen_motiontrail3d__")

                        root_channels = root.animation_data.action.groups["__gen_motiontrail3d__"].channels
                        #just a check to ensure channels are in the above order..
                        #print([f'{channel.data_path}[{channel.array_index}]' for channel in root_channels])
                        for channel in root_channels:
                            channel.convert_to_samples(self.frame_start,self.frame_end+1)
                            #print('total samples: ' +str(len(channel.sample_points)))
                        
                        #print_time('H')
                        #print('recalc-ed parent')
                        self.relative_parent_is_valid=True 
                        #####self.current_relative_parent_matrix =  parent_object.matrix_world.copy()
                        #####self.all_control_points_root.matrix_world = self.current_relative_parent_matrix.copy()
                                                     
                        for i in range(0,frames_length):
                            
                            #print_time('H1')
                            bpy.context.scene.frame_set(i + frame_start)
                            parent_matrix_world = parent_object.matrix_world
                            #print_time('H2')
                            inverse_matrix = parent_matrix_world.inverted() 
                            #print_time('H3')
                            self.relative_parent_inverse_matrix_cache[i] = inverse_matrix
                            #print_time('H4')
                            self.active_parent_matrix_cache[i] = inverse_matrix @ self.nonrelative_parent_matrix_cache[i]
                            #print_time('H5')
                            #active cache set such that all sample pts and ctrls are relative to the relative_parent at the current frame.
                            #self.active_parent_matrix_cache[i] = current_parent_world @ self.parent_matrix_cache[i] 

                            #print_time('H6')
                            ploc,prot,pscale = parent_matrix_world.decompose()
                            #print_time('He7')
                            pscale=(1,1,1)
                            for axis in range(0,3):
                                channel = root_channels[axis]
                                co = channel.sampled_points[i].co
                                co[1] = ploc[axis]
                            for axis in range(0,4):
                                channel = root_channels[3 + axis]
                                co = channel.sampled_points[i].co
                                co[1] = prot[axis]
                            for axis in range(0,3):
                                channel = root_channels[7 + axis]
                                co = channel.sampled_points[i].co
                                co[1] = pscale[axis]
                            #print_time('H8')
                        
                        ####self.all_control_points_root.parent = parent_object
                        ####self.all_control_points_root.parent_bone = ''
                        ####self.all_control_points_root.parent_type = 'OBJECT'
                        ####self.all_control_points_root.matrix_parent_inverse = Matrix.Identity(4)
                                
                        bpy.context.scene.frame_set(current_frame)
            else:
                #print_time('I')
                #setting root parent doesnt work, results in moving ctrls towrads infinity
                self.relative_parent_is_valid=False 
                ####self.all_control_points_root.parent = None
                ####self.all_control_points_root.parent_bone = ''
                ####self.all_control_points_root.parent_type = 'OBJECT'
                #####self.current_relative_parent_matrix = Matrix.Identity(4)
        
                root = self.all_control_points_root
                root.animation_data_clear()
                root.matrix_world = Matrix.Identity(4)#self.current_relative_parent_matrix.copy()
                ####self.all_control_points_root.matrix_parent_inverse = Matrix.Identity(4)
                            
            for i in range(0,frames_length):
                self.parent_positions[i] = self.active_parent_matrix_cache[i].to_translation()

            #print_time('J')
            #self.recalculate_triple_buffer(settings,force_relink=True) 
            
            self.ignore_control_update_once=True
            self.allowed_control_update.clear()
            self.active_trail_data.clear_updated()
            #bugfix: read smaple points before cal control worlds so that offsetted controls will use updated tracking point matrices.
            self.read_sample_points()
            self.calculate_control_worlds()
            
            #print_time('Jquelin')
            self.sync_time_ctrl_locations() 
            #print_time('K')
            

            self.report({'INFO'},'[{0}] Relative Parent flag change processed..'.format( self.target_name))
            print_conditional(debug_enable_print_func_tags ,'..end relative_parent_check_flags_change')
            return True 
        
        print_conditional(debug_enable_print_func_tags ,'... relative_parent_check_flags_change')
        return False 
    def relative_parent_sync_dependency_matrices(self):
    
        settings = bpy.context.scene.motion_trail3D_settings
        frame_start,frame_end = self.frame_start,self.frame_end 
        frames_length  = frame_end-frame_start + 1
        
        #ex: camera is rel. parent and a trail, so we want to be able to edit the camera and a character IK simultaneously.\
        #this code reads the camera's real time matrices
        if self.relative_parent_is_valid:
            
            
            valid_dependency_targets = {trail.target_name:trail for trail in settings.active_trails}
            
            dependency_trail = None 
            if settings.relative_parent_object in bpy.data.objects:
                parent_object = bpy.data.objects[settings.relative_parent_object]
                if isinstance(parent_object.data,bpy.types.Armature) and len(settings.relative_parent_bone) > 0:
                    if settings.relative_parent_bone in valid_dependency_targets:
                        dependency_trail = valid_dependency_targets[settings.relative_parent_bone]
                elif settings.relative_parent_object in valid_dependency_targets:
                        dependency_trail = valid_dependency_targets[settings.relative_parent_object]
                
                #there exists a trail for relative parent target
                if (dependency_trail is not None) and dependency_trail.hierarchy_has_updated:
                    #print_time('dep has updated. ' + self.target_name)
                    
                    child_dependency_matrices = dependency_trail.child_dependency_matrices

                    root = self.all_control_points_root                    
                    root_channels = root.animation_data.action.groups[TAG_root_action_group].channels

                    #print_time('writing to anim probably leads to snapping')
                    for i in range(0,frames_length):
                        parent_matrix = child_dependency_matrices[i].get()
                        inverse_matrix = parent_matrix.inverted()

                        self.relative_parent_inverse_matrix_cache[i] = inverse_matrix
                        self.active_parent_matrix_cache[i] = inverse_matrix @ self.nonrelative_parent_matrix_cache[i]

                        ploc,prot,pscale = parent_matrix.decompose()
                        pscale = (1,1,1)
                        for axis in range(0,3):
                            channel = root_channels[axis]
                            co = channel.sampled_points[i].co
                            co[1] = ploc[axis]
                        for axis in range(0,4):
                            channel = root_channels[3 + axis]
                            co = channel.sampled_points[i].co
                            co[1] = prot[axis]
                        for axis in range(0,3):
                            channel = root_channels[7 + axis]
                            co = channel.sampled_points[i].co
                            co[1] = pscale[axis]
                            
                    #implementation note: overwriting root sample points does not sync the root to the trail
                    #so we just snap it here.
                    root.matrix_world = child_dependency_matrices[self.current_frame_to_index()].get()
                    root.scale=(1,1,1)
                            
                            
                    #bugfix: due to object parenting, when camera updated, so is this trail. Therefore, allowed_control_update will contain all shown controls which means calculate control worlds won't update their camera-relative position.
                    #and so we clear the buffer so they are updated.
                    #Without this, it lead to a bug where animating Camera directly in GE or inserting keys did not move all the controls correctly, but moving the Camera or self controls did.
                    #it makes sense, moving the controls doesn't lead to the Cam/Self obj hierarchy being updates and so the allowed list isn't filled.
                    #Q)but what isn't explained is why the desynced controls were only that which were time-near the edited keyframes (not through ctrls), and others were synced just fine.
                    #A) because those not near would already have the correct cam-relative xform and thus don't need to be resynced.

                    #this prevents trails that depend on the relative parent from being move with the parent.
                    #currently it doesn't seem to be useful or intuitive to do so anyways, so not considered a bug.
                    self.allowed_control_update.clear()
                    self.calculate_control_worlds()
                    self.ignore_control_update_once=True
                    
                    #print_time('bobby')
                    self.read_sample_points()
                    self.sync_time_ctrl_locations() 

                    active_trail_data = self.active_trail_data
                    active_trail_data.updated_objects.clear()
                    active_trail_data.updated_time_objects.clear()
                    active_trail_data.prev_updated_time_objects.clear()

        return False 
    def check_trail_mode_changed(self):
        #bug: on undo, I think active trail isn't undone. So pre trail data could be loc but pre trail mode may be rot.
        #print_undocheck(f'pre:{self.prev_trail_mode} pre data:{self.prev_trail_data.mode if self.prev_trail_data else ""}')
        settings = bpy.context.scene.motion_trail3D_settings
        
        cur_trail_mode = self.get_trail_mode()
        changed_trail_mode = self.prev_trail_mode != cur_trail_mode 
        self.prev_trail_mode=cur_trail_mode 

        cur_rot_mode = self.target.rotation_mode 
        changed_rot_mode = self.prev_rotation_mode != cur_rot_mode
        self.prev_rotation_mode = cur_rot_mode

        changed_trail_data = changed_trail_mode or (cur_trail_mode == 'ROTATION' and changed_rot_mode) or self.active_trail_data is None 

        if changed_trail_data:
            self.prev_trail_data = self.active_trail_data
            self.active_trail_data = self.trail_location_data if cur_trail_mode =='LOCATION' else self.trail_rotation_data[self.target.rotation_mode]
            print_undocheck(f'mode change: pre:{self.prev_trail_data.mode if self.prev_trail_data else "NONE"} cur:{self.active_trail_data.mode if self.active_trail_data else "NONE"}')

        return changed_trail_data

    def clean_ctrl_objects(self):
        #optimization check: this can take a whole ms/call, even if ctrl has no animation_data.
        if bpy.context.tool_settings.use_keyframe_insert_auto:
            for obj_wrapper in self.object_pool.buffer:
                if obj_wrapper.exists():
                    obj = obj_wrapper.deref()
                    if is_ctrl_used(obj):#obj['in_use'] == True:
                        if obj.animation_data:
                            obj.animation_data_clear()
                            #print('had animation data: ' + obj.name)
    def validate_objects(self):
        self.clean_ctrl_objects()
        #return True

        #error occurs when new empties created then user undos.
        #Reproduce: start with 1 key. init trail. create another key (results in new pooled objects).expand ctrls root. undo. Error related to ref to deleted-by-undo object
        
        self.all_control_points_root = ctrl_root = self.ptr_all_control_points_root.deref()
        settings = bpy.context.scene.motion_trail3D_settings
        total_pooled_objects = len(self.object_pool.buffer)
        total_existing_objects = len(ctrl_root.children)
        
        #user undo resulted in deleted object
        #print('total in use: ' +  str(total_existing_objects) + '__' + time_string())
        pool = self.object_pool
        #print('pool size: {0} at time {1}'.format(total_pooled_objects,time_string()))
        if total_pooled_objects > total_existing_objects:
            #print_time('validated trail')
            #print('detected undo that deleted pooled objects.. recreating data' + time_string())
            #
            print_undocheck('validation fail: total pooled > existing')
            removed_indices = []
            for i,obj  in enumerate(pool.buffer):
                if not obj.exists():
                    removed_indices.append(i)
                    #print('...detected: ' + obj.name)
            for k in reversed(removed_indices):
                del pool.buffer[k]

            pool.capacity = len(pool.buffer)
            in_use = 0
            for obj in pool.buffer:
                if is_ctrl_used(obj.deref()): #obj.deref()['in_use']:
                    in_use += 1 
            pool.in_use=in_use 

            
            #need to ensure correct active trail set for self.get_target_default_value 
            #otherwise, error would be raised on changing from loc (0 keys) to rot (3 keys) mode then undoing.
            #commented out since we check for trail mode change before obj validation anyways
            #self.check_trail_mode_changed()

            #force_relink will also clear updated updates to avoid loc value and time writes
            self.recalculate_triple_buffer(settings,force_relink=True,preserve_selection= False) 
            self.ignore_control_update_once=True
            self.allowed_control_update.clear()
            #print('have..i found it..')
            self.read_sample_points()
            self.sync_time_ctrl_locations()
            #print('in_use: ' + str(in_use))
            #print('______recreation count: ' + str(len(ctrl_root.children)))
            return False 
        if total_pooled_objects < total_existing_objects:
            print_time('validated trail')
            #print('..more existing than pooled!' + time_string())
            
            print_undocheck('validation fail: total pooled < existing')
            pooled_names = set()
            for obj in pool.buffer:
                pooled_names.add(obj.name)

            added = []
            for child in ctrl_root.children:
                if child.name not in pooled_names:
                    added.append(child)
            for child in added:
                pool.realloc(child) 
                
            #need to ensure correct active trail set for self.get_target_default_value
            #commented out since we check for trail mode change before obj validation anyways
            #self.check_trail_mode_changed()

            self.recalculate_triple_buffer(settings,force_relink=True,preserve_selection=False) 
            self.ignore_time_sync_once = True
            self.ignore_control_update_once=True
            self.allowed_control_update.clear()
            #print('have..i found it..1')
            self.read_sample_points()
            self.sync_time_ctrl_locations()

            return False 
        return True 

    def deref_channels(self):
        
            active_trail_data = self.active_trail_data

            #redundant double deref() for rotation and location, not that big of a deal
            #location should always be deref()-ed so we can read sample points
            #consider: although I could check if active trail data is rotation, that only improves performance, not any behaviour. 
            #deref active trail first to get correct result()
            result = active_trail_data.deref_channels()
            self.trail_location_data.deref_channels()

            for channel_index,ptr_channel in enumerate(self.ptr_channels_location):
                self.channels_location[channel_index] = None 
                if ptr_channel.exists():
                    self.channels_location[channel_index] = ptr_channel.deref()
                    
            for channel_index,ptr_channel in enumerate(self.ptr_channels_scale):
                self.channels_scale[channel_index] = None 
                if ptr_channel.exists():
                    self.channels_scale[channel_index] = ptr_channel.deref()
                    
            for rotation_mode,ptr_channels in self.ptr_channels_rotation.items():
                for channel_index, ptr_channel in enumerate(ptr_channels):
                    self.channels_rotation[rotation_mode][channel_index] = None 

            rotation_mode = self.target.rotation_mode 
            for channel_index, ptr_channel in enumerate(self.ptr_channels_rotation[rotation_mode]):
                self.channels_rotation[rotation_mode][channel_index] = None 
                if ptr_channel.exists():
                    self.channels_rotation[rotation_mode][channel_index] = ptr_channel.deref()  

            
            rot = self.target.rotation_quaternion
            self.target_rotations['QUATERNION'] = [rot[0],rot[1],rot[2],rot[3]]
            rot = self.target.rotation_axis_angle
            self.target_rotations['AXIS_ANGLE'] = [rot[0],rot[1],rot[2],rot[3]]
            rot = self.target.rotation_euler
            self.target_rotations['XYZ'] = [rot[0],rot[1],rot[2]]      
            rot = self.target.rotation_euler
            self.target_rotations['XZY'] = [rot[0],rot[1],rot[2]]          
            rot = self.target.rotation_euler
            self.target_rotations['YXZ'] = [rot[0],rot[1],rot[2]]         
            rot = self.target.rotation_euler
            self.target_rotations['YZX'] = [rot[0],rot[1],rot[2]]           
            rot = self.target.rotation_euler
            self.target_rotations['ZXY'] = [rot[0],rot[1],rot[2]]      
            rot = self.target.rotation_euler
            self.target_rotations['ZYX'] = [rot[0],rot[1],rot[2]]  

            return result 
    def deref(self):
        
        self.active_trail_data.deref()

        self.active_object = self.ptr_active_object.deref()
        self.action = self.ptr_action.deref()

        self.all_control_points_root = self.ptr_all_control_points_root.deref() 

    def debug_invalidate_references(self):
    
        self.channels_location[0] = None
        self.channels_location[1] = None
        self.channels_location[2] = None
        for rot_mode,channels in self.channels_rotation.items():
            for i in range(0,len(channels)):
                channels[i] = None 
        self.channels_scale[0] = None
        self.channels_scale[1] = None
        self.channels_scale[2] = None
        self.active_object = None 
        self.action =None
        self.all_control_points_root=None
    
        self.debug_crash_check_check_control_offset_change()
        self.debug_crash_check_apply_trail_dependency_flags_change()
        self.debug_try_crash_relative_parent_check_flags_change()

    
    def update_control_hide_locked(self,settings):
        #this works, but in its current state doesn't update while animation playing since we don't check for locked
        #we could just call the func from draw() but that seems like too much extra processing for something minimal
        #--
        #besides that, what if user wanted to change handle type? It's convenient if the ctrl is showing. Attempts to move them
        #will highlight the key, thus the user can easily change the handle type. If its auto hidden, then user must manually find and select keys and handles.
        return
        active_trail_data = self.active_trail_data
        key_objects =active_trail_data.key_objects
        key_time_objects =active_trail_data.key_time_objects

        #works but not active because of built in hassle of setting a coilumn of handle types.. so it'd lead to more messing around just to get the handle to show up or hide it which is counter productive.
        #problem with this is that it would on
        if self.show_handles:
            #todo: do same for time controls
            triplet_buffer = active_trail_data.triplet_buffer 
            channels = active_trail_data.channels 
            for i,triplet in enumerate(triplet_buffer):
                handle_left_free = False
                handle_right_free = False
                for channel_index,channel in enumerate(channels):  
                    if triplet[channel_index] is not None:
                        channel_key_index = triplet[channel_index]
                        keyframe_point = channel.keyframe_points[channel_key_index]
                        #convenience selection of value objects to quickly allow going back and forth from graph editor to view3D.
                        #it would be inconvenient to also select the time objects since those xforms are likely less frequent and
                        #user may only want to modify exclusively value or time objects. For now, default to only auto select value objects.
                        handle_left_free =  handle_left_free  or keyframe_point.handle_left_type  in ('FREE','ALIGNED') 
                        handle_right_free =  handle_right_free  or keyframe_point.handle_right_type  in ('FREE','ALIGNED')
                        
                #todo: unfinished
                result = (not handle_left_free) 
                if key_objects.left[i].hide_viewport != result: key_objects.left[i].hide_viewport = result
                key_time_objects.left[i].hide_viewport = (not handle_left_free) or not self.show_time
                
                key_objects.right[i].hide_viewport = (not handle_right_free) 
                key_time_objects.right[i].hide_viewport = (not handle_right_free) or not self.show_time

    def update_control_hide(self,settings,force=False):
        active_trail_data = self.active_trail_data
        key_objects =active_trail_data.key_objects
        key_time_objects =active_trail_data.key_time_objects

        render_trail = self.get_trail_info().render_trail and settings.render_trail
        show_time = settings.show_time and render_trail 
        show_co = settings.show_co and render_trail 
        show_handles = settings.show_handles and render_trail   


        if not self.is_rotation_mode():
            if force or (self.show_time != show_time):
                self.show_time = show_time

                hide = not self.show_time
                for control_type,group in enumerate(key_time_objects.grouped):
                    for triplet_index,obj in enumerate(group):
                        #hide_viewport = True means Alt+H wont show the control again, trail-hidden controls stay hidden.
                        obj.hide_viewport = hide 
        
        if force or  (self.show_co != show_co):
            self.show_co = show_co
        
            hide = not self.show_co
            for triplet_index,obj in enumerate(key_objects.co):
                #hide_viewport = True means Alt+H wont show the control again, trail-hidden controls stay hidden.
                obj.hide_viewport = hide 
                
        if force or (self.show_handles != show_handles):
            self.show_handles = show_handles

            hide = not self.show_handles
            for triplet_index, obj in enumerate(key_objects.left):
                #hide_viewport = True means Alt+H wont show the control again, trail-hidden controls stay hidden.
                obj.hide_viewport = hide 
            for triplet_index, obj in enumerate(key_objects.right):
                #hide_viewport = True means Alt+H wont show the control again, trail-hidden controls stay hidden.
                obj.hide_viewport = hide 
            self.update_control_hide_locked(settings)
                
        if (self.show_hidden_co != settings.show_hidden_co):
            self.show_hidden_co = settings.show_hidden_co
            for triplet_index, obj in enumerate(key_objects.co):
                obj.hide_set(False)  
        if (self.show_hidden_handles != settings.show_hidden_handles):
            self.show_hidden_handles = settings.show_hidden_handles
            for triplet_index, obj in enumerate(key_objects.left):
                obj.hide_set(False)  
            for triplet_index, obj in enumerate(key_objects.right):
                obj.hide_set(False)  

        if (self.show_hidden_time != settings.show_hidden_time):
            self.show_hidden_time = settings.show_hidden_time
            for triplet_index, obj in enumerate(key_time_objects.left):
                obj.hide_set(False)  
            for triplet_index, obj in enumerate(key_time_objects.co):
                obj.hide_set(False)  
            for triplet_index, obj in enumerate(key_time_objects.right):
                obj.hide_set(False)  

        settings_scale = self.get_controller_scale()
        if self.controller_scale != settings_scale:
            self.controller_scale = settings_scale

            for group in key_objects.grouped:
                for obj in group:
                    obj.empty_display_size = settings_scale
            for group in key_time_objects.grouped:
                for obj in group:
                    obj.empty_display_size = settings_scale * 5.0/4.0


        

        
    update_types = ['ACTION', 'ARMATURE', 'BRUSH', 'CAMERA', 'CACHEFILE', 'CURVE', 'FONT', 'GREASEPENCIL', 'COLLECTION', 'IMAGE', 'KEY', 'LIGHT', 'LIBRARY', 'LINESTYLE', 'LATTICE', 'MASK', 'MATERIAL', 'META', 'MESH', 'MOVIECLIP', 'NODETREE', 'OBJECT', 'PAINTCURVE', 'PALETTE', 'PARTICLE', 'LIGHT_PROBE', 'SCENE', 'SOUND', 'SPEAKER', 'TEXT', 'TEXTURE', 'WINDOWMANAGER', 'WORLD', 'WORKSPACE']
    tmp_updated_objects = set()
    def scene_update(self,scene,depsgraph):
        
        print_conditional(debug_enable_print_func_tags ,'start scene update...')

        #print_time(f'scene: {scene.name}')
        #self.debug_invalidate_references()

        #print_time('scene_after debug check')
        view_layer = depsgraph.view_layer
        #print_conditional(True ,'scene')#:{scene.name} view_layer:{depsgraph.view_layer.name} count:{len(view_layer.objects)}')
        
        #if self.buffered_framed_set is not None:
        #    bpy.context.scene.frame_set(bpy.context.scene.frame_current)
        #    self.buffered_framed_set = None 
            
        #bug: at 60fps, this func isn't even called frequently, thats why realtime updates fail while animation playing at 60fps.
        update_types =self.update_types
        settings = scene.motion_trail3D_settings
        
        
        active_trail_data = self.active_trail_data
        
            
        #print_time('is active? : ' + str(self.is_active_get()))
        if not self.is_active_get():
            print_time('not active, returning. Scene update.')
            if not self.is_disposed:
                #print('possible undo detected or window lost. Disposing motion trail. Scene')
                self.dispose()
            return 


        render_trail = self.get_trail_info().render_trail  and  settings.render_trail
        if not render_trail:
            return 

            
        if not self.validate_trail(bpy.context):
            print_time('trail failed to validate, returning. Scene update.')
            return 

        #target_updated = False
        action_updated = False 
        for update in bpy.context.view_layer.depsgraph.updates:
            #print_time(f'id:{update.id} is_updated_geo:{update.is_updated_geometry} is_updated_transform:{update.is_updated_transform}')

            
            #is_ctrl_used(): besides knowing its a trail ctrl, it may be hidden due to realloc, therefore it has invalid data so don't use it.
            if update.is_updated_transform and is_ctrl_used(update.id):
                #print_time(f'trail:{self.target_name} updated:{update.id.name} \n\tparent:{update.id.parent} \n\tpart of trail?{update.id.parent.name == self.all_control_points_root.name}')
                #print_time(self.all_control_points_root.name)
                #filter to only ctrls part of trail, above condition True for all trail ctrls, indep. of target
                if update.id.parent and (update.id.parent.name == self.all_control_points_root.name):
                    self.tmp_updated_objects.add(update.id)
            action_updated = action_updated or (update.id.name == self.ptr_action.name and isinstance(update.id,bpy.types.Action))
            #if not self.ignore_control_update_once:
            #print_time('raw updated: ' + update.id.name)
            #if  self.ignore_control_update_once and len(self.allowed_control_update) == 0:
            #    print_time('ignored yet allowed is empty??: ' + update.id.name + '  ' + time_string())
        
        updated_objects = active_trail_data.updated_objects
        updated_time_objects = active_trail_data.updated_time_objects
        key_objects = active_trail_data.key_objects
        key_time_objects = active_trail_data.key_time_objects

        #key_time_objects.deref()
        #key_objects.deref()

        
        ##print_time('end crash?')

        #self.debug_test += 1

        #clear at start of scene update instead of after processing trail data.
        #Process trail data and draw's time ctrl move are only funcs that use update buffers
        #former occurs directly after this so not a problem to keep the buffer around. - error checks will clear buffer if invalidated (on forced recalc buffer)
        #latter should still be fine due to error checks
        active_trail_data.clear_updated()


        #print('0')
        if not self.ERROR_motion_trail:
            try:
                #avoid circular updates when we sync fcruve data to object data
                currently_ignoring = self.ignore_control_update_once
                if self.ignore_control_update_once:
                    self.ignore_control_update_once=False
                    #print_time('no longer ignoring')

                    #if len(self.allowed_control_update) == 0:
                    #    print('---ignored and nothing being draggged')
                    #if len(self.allowed_control_update) > 0:
                    #    print('---ignored and something being draggged: ' + str(self.allowed_control_update))
                    #for update in bpy.context.depsgraph.updates:
                    #    if update.is_updated_transform:
                    #        print('ignore--' + update.id.name)
        

        
                if currently_ignoring and len(self.allowed_control_update) > 0:
                                
                    #if self.debug_just_snapped:
                    #    self.debug_just_snapped=False
                    #    print_conditional(debug_general,'just snapped, returning (scene update) 1st')
                    #    return 
                    #print('1')
                    
                    for updated_object in self.tmp_updated_objects:
                        triplet_index = updated_object[TAG_triplet_index]
                        control_type = updated_object[TAG_control_type]
                        value_type = updated_object[TAG_value_type]

                        if updated_object.name in self.allowed_control_update:
                            if (value_type & BIT_value_type_value):
                                updated_objects.ptr_grouped[control_type].add(key_objects.ptr_grouped[control_type][triplet_index])
                                updated_objects.grouped[control_type].add(key_objects.grouped[control_type][triplet_index])
                            
                            if (value_type & BIT_value_type_time):
                                updated_time_objects.ptr_grouped[control_type].add(key_time_objects.ptr_grouped[control_type][triplet_index])
                                updated_time_objects.grouped[control_type].add(key_time_objects.grouped[control_type][triplet_index])
                        
                elif not currently_ignoring:
                    
                    #if self.debug_just_snapped:
                    #    self.debug_just_snapped=False
                    #    print_conditional(debug_general,'just snapped, returning (scene update) 2nd')
                    #    return 
                    #While ctrl dragged, every step after will ignore indirectly affected ctrls by user.
                    #when dragging finished, ctrls are no longer ignored so we begin tracking them again.
                    #implementation: question: q:[1/2/20] I don't remember the exact use case for allowed_control_updates... but it appears to be used to avoid reading ctrl worlds when the contrl is being dragged?
                    #but what's the case where there is such a conflict? Maybe for aligned handles, to avoid considering them dragged by user when trail is just aligning the opposite handle or dragging the CO?
                    self.allowed_control_update.clear()
                    #print('1')
                    for updated_object in self.tmp_updated_objects:
                        triplet_index = updated_object[TAG_triplet_index]
                        control_type = updated_object[TAG_control_type]
                        value_type = updated_object[TAG_value_type]

                        if (value_type & BIT_value_type_value):
                            
                            updated_objects.ptr_grouped[control_type].add(key_objects.ptr_grouped[control_type][triplet_index])
                            updated_objects.grouped[control_type].add(key_objects.grouped[control_type][triplet_index])
                        
                        if (value_type & BIT_value_type_time):
                            updated_time_objects.ptr_grouped[control_type].add(key_time_objects.ptr_grouped[control_type][triplet_index])
                            updated_time_objects.grouped[control_type].add(key_time_objects.grouped[control_type][triplet_index])
                        
                        self.allowed_control_update.add(updated_object.name)
                        
                

                #if self.debug_just_snapped:
                #    self.debug_just_snapped=False
                #    print_conditional(debug_general,'just snapped, returning (scene update) 3rd')
                #    return 
                #print(time_string())
                #for i,k in enumerate(update_types):
                #    if bpy.context.depsgraph.id_type_updated(k):
                #        print('updated: ' + k)
                #print()
                despgraph = bpy.context.view_layer.depsgraph
                #if not (self.active_object.name in self.tmp_updateaaad_objects):
                #    print('----------------------------------------------------------------')
                
                #when bone moved or bone data updated, it's the armature that gets updated, not the object
                target_active_obj = self.ptr_active_object.deref()
                target_updated = (self.ptr_active_object.name in self.tmp_updated_objects) or (target_active_obj.data and target_active_obj.data.name in self.tmp_updated_objects)
                #print(target_updated)

                #doesn't matter if owner obj or bone updated. Only matters if action updated. This should imrpove perf when anim playing, removes redundant writes to controls
                if action_updated:# or  (target_updated and (despgraph.id_type_updated('ACTION') or despgraph.id_type_updated('ARMATURE') or despgraph.id_type_updated('OBJECT')))  :
                    self.updated_active_object=True
                    #self.read_sample_points()
                    #print_time('target updated: ' + self.active_object.name)
                

                value_objects_changed  =  len(updated_objects.ptr_left) > 0 or len(updated_objects.ptr_co) > 0 or len(updated_objects.ptr_right) > 0
                time_objects_changed  =  len(updated_time_objects.ptr_left) > 0 or len(updated_time_objects.ptr_co) > 0 or len(updated_time_objects.ptr_right) > 0
                any_objects_changed  =  value_objects_changed or time_objects_changed
                info = self.get_trail_info()
                info.has_updated=any_objects_changed or self.updated_active_object



                #if self.debug_just_snapped:
                #    self.debug_just_snapped=False
                #    print_conditional(debug_general,'just snapped, returning (scene update)')
                #    return 
                #if (len(self.tmp_updated_objects) > 0) or self.updated_active_object:
                #    for area in bpy.context.screen.areas:
                #        area.tag_redraw()
                self.tmp_updated_objects.clear()
                self.process_trail_updates(bpy.context)
            except Exception as e:
                self.ERROR_motion_trail=True
                #print(e)
                import traceback
                msg = traceback.format_exc()
                self.report(type={'ERROR'},message=msg)
                print_time('[ERROR] : ' + msg)
        #print_conditional(debug_enable_print_func_tags or True,'...end scene update')
    def dependency_trailOp_get(self):
        settings = bpy.context.scene.motion_trail3D_settings
        info = self.get_trail_info()
        dep_target_name = info.dependency.target_name 

        for trailOp in settings.active_trails:
            if dep_target_name == trailOp.target_name:
                return trailOp 
            
        return None 
    def draw_callback_px(self):
            
        if crash_stop_everything:
            print_time('CSE draw callback ')
            return 

        print_conditional(debug_enable_print_func_tags ,'start draw callback...')
        if not self.ERROR_motion_trail:
            try:
                context = bpy.context
                settings = context.scene.motion_trail3D_settings
                
                if not self.is_active_get():
                    print_time('not active, returning. Render.')
                    if not self.is_disposed:
                        print_time('possible undo detected past trail init or window lost. Disposing motion trail. Render')
                        self.dispose()
                    return 


                #must return if not valid. Only some data will have been validated, but not all.
                #Next func that calls validate will validate more data. 
                if not self.validate_trail(context):
                    print_time('trail failed to validate, returning. Draw callback.')
                    return 
                #print_time('after validation')
                #this does increase scene_update rate, but there is still a hard limit of: if fps not hit, then scene_update not called.
                render_trail = self.get_trail_info().render_trail  and  settings.render_trail
                if render_trail:
                    
                    
                    #False when frame change using jump key (desirable)
                    if  bpy.context.screen.is_animation_playing:
                            
                        if  settings.increased_ctrl_update_while_playing:
                            #print_time('increasing scene_update rate')
                            #self.all_control_points_root.location = self.all_control_points_root.location
                            self.target.id_data.location = self.target.id_data.location 

                        if settings.increased_fcurve_update_while_playing:
                            #to sync fcurve changed to trail
                            self.read_sample_points() 
                    

                self.render(context)
            except Exception as e:
                self.ERROR_motion_trail=True
                #print(e)
                import traceback
                msg = traceback.format_exc()
                self.report(type={'ERROR'},message=msg)
                print_time('[ERROR] : ' + msg)
        print_conditional(debug_enable_print_func_tags  ,'...end draw')
    def validate_trail(self,context):
        
        validation_count = 0
        max_count = 10

        #prevents blank render on undo/redo
        while(validation_count < max_count):
            validation_count += 1

            settings = context.scene.motion_trail3D_settings
            #placed this early since used by check_trail_mode_changed and deref_channels() if mode==ROTATION
            self.target = self.ptr_target.deref()
            #active mode needs to be set before we validate objects or deref channels
            if self.check_trail_mode_changed():
                self.active_trail_data.clear_updated()
                self.deref_channels() 
                #note: don't deref() new trail objects if they haven't been linked yet..

                #needs to be checked  since mode change may create objects
                #so objs need to be validated before recalculating triplet buffer
                if self.validate_objects():
                    #objects were still valid
                    self.recalculate_triple_buffer(settings,force_relink=True) 
                    self.read_sample_points()
                    self.sync_time_ctrl_locations()
                    self.ignore_control_update_once=True 
                    print_time('Failed Validate Trail. Trail mode changed')
                    continue
                else:
                    print_time('Failed Validate Trail. Trail mode changed and objects not valid.')
                    
                #print('mod')
                continue
            if not self.deref_channels():
                #placed here for bugfix: Case on undoing resulting in deletion of newly added pool items (ex: adding an 8th triplet then undoing). Where deref() will error due to removed object so we have to validate objects before that.
                if not self.validate_objects():
                    print_time('Failed Validate Trail. Animation channels invalid and objects not valid.')
                    self.updated_active_object=True
                    self.ignore_control_update_once=True 
                    continue
                else:
                    print_time('Failed Validate Trail. Animation channels invalid.')
                self.deref()
                self.recalculate_triple_buffer(settings) 
                self.read_sample_points()
                self.sync_time_ctrl_locations()
                continue
                
            if not self.validate_objects():
                print_time('Failed Validate Trail. Objects not valid.')
                self.updated_active_object=True
                self.ignore_control_update_once=True 
                #print('va')
                continue


            if self.has_undo_occured():
                print_undocheck('undo has detected (process trail updates)..')
                print_time('Failed Validate Trail. Undo detected.')
                data_changed = True 
                self.ignore_control_update_once=True 
                self.recalculate_triple_buffer(settings,force_relink=True,preserve_selection=False)
                #ensure drawn sample points update, mostly so it doesn't appear to be bugged.
                #without this, the ctrl obj would be correctly placed but the trail rendered point wouldn't have been updated yet.
                self.read_sample_points()
                self.sync_time_ctrl_locations()
                #return to avoid time writes, to avoid a bug where time objs will be updated and processed as if they moved to world Zero
                #print('undd')
                continue
                
            self.deref()        
            
            #len_xKeys = len(self.channels_location[0].keyframe_points) if self.channels_location[0] else 0
            #len_yKeys = len(self.channels_location[1].keyframe_points) if self.channels_location[1] else 0
            #len_zKeys = len(self.channels_location[2].keyframe_points) if self.channels_location[2] else 0


            #num_keys_changed = False
            #if (len_xKeys != self.cached_len_xKeys) or (len_yKeys != self.cached_len_yKeys )or (len_zKeys != self.cached_len_zKeys):
            #    num_keys_changed=True
            #    self.cached_len_xKeys,self.cached_len_yKeys,self.cached_len_zKeys = len_xKeys,len_yKeys,len_zKeys
            #    print_time('key count changed..')
            #    self.ignore_control_update_once=True
            #    self.recalculate_triple_buffer(settings,force_relink=True) 
            #    self.read_sample_points()
            #    self.sync_time_ctrl_locations()
            #    return  False

            ##print('beef')
            self.update_control_hide(settings)

            ##print('salmon')
            #self.apply_trail_dependency_due_parent_xformed()
            ##print('chicken')
            #self.apply_relative_parent_due_frame_change() 
            #
            ##print('vegetables')
            if self.check_control_offset_change():
                print_time('Failed Validate Trail. Control offset changed.')
                continue
                

            return True

        return False 

    def timer_snap_controls(self,target_name):
        
        print_conditional(debug_enable_print_func_tags,'timer_snap_controls... snapsnapsnapsnapsnapsnap')
        #if trail disposed, this func isn't called anyways.

        #if trail disposed, do nothing.
        #without this, crashes may occur that may be hard to track due to delay.
        if target_name not in trail_callbacks:
           print_conditional(debug_general,'prevented delay snap.')
           return None 

        self.total_timers -= 1
        #self.debug_test += 1
        #self.apples -= 1
        #total_timers[self.target_name] -= 1
        #if there is a buffer of timers to call, then don't snap.
        #it means user has moved some controls.
        #print_time('why does this cause a scene update and move all objects...')
        if self.total_timers == 0:
            if self.validate_trail(bpy.context):

                #if len(self.allowed_control_update) > 0:
                #    self.total_timers=1
                #    print_time('still updating... delaying snap further.')
                #    return 100.0/1000.0 
                #bug ..call multiple times even after so many prop edits?
                #Question: If we move a ctrl in scene update. Does that propagate to another scene update?
                #That was the reason for ctrl ignoring right? If moved ctrl in draw, then it caused another scene udpate, thus anothe rdraw, forever
                #but.. it seems like there is no infinite loop. And thus no more need for ctrl ignoring?
                print_conditional(debug_general,'snapsnapsnapsnapsnapsnap' + repr(self.total_timers))
                
                settings = bpy.context.scene.motion_trail3D_settings

                self.ignore_control_update_once = True
                self.allowed_control_update.clear()
                for objs in self.active_trail_data.prev_updated_time_objects.grouped:
                    for obj in objs:
                        #print(obj.name)
                        self.allowed_control_update.add(obj.name)
                self.active_trail_data.clear_updated()
                self.recalculate_triple_buffer(settings) 
                self.sync_time_ctrl_locations()
                #self.debug_just_snapped = True
            

        
        print_conditional(debug_enable_print_func_tags,'.. timer_snap_controls')
        return None 
    def delayed_snap(self):
         
        interval = 100.0/1000.0 
        #use longer time to avoid tiny apparent lag (snapping) when user trying to make tiny adjustments
        if bpy.context.scene.tool_settings.use_proportional_edit_objects and bpy.context.mode != 'POSE':
            interval = 500.0/1000.0

        #bpy.app.timers.register(self.timer_snap_controls,first_interval=interval)
        bpy.app.timers.register(functools.partial(POSE_OT_CustomMotionTrail.timer_snap_controls,self,self.target_name),first_interval=interval)#100.0/1000.0)
        #if I comment this out, then all obj's won't be erroneously xform-updated....WHY...
        self.total_timers += 1
        #print('should happen before timer called') 
                    
    def process_trail_updates(self,context):

        #if self.debug_just_snapped:
        #    self.debug_just_snapped=False
        #    print_conditional(debug_general,'just snapped, returning (process trail updates)')
        #    return 
        #Q: is there a good reason to keep process trail updates in draw callback?
        print_conditional(debug_enable_print_func_tags ,'process trail updates...')
        #placed this early since used by check_trail_mode_changed and deref_channels() if mode==ROTATION
       
        settings = context.scene.motion_trail3D_settings


        target = self.target
        active_trail_data = self.active_trail_data
        updated_objects = active_trail_data.updated_objects
        updated_time_objects = active_trail_data.updated_time_objects
        prev_updated_time_objects = active_trail_data.prev_updated_time_objects


        #order of these two funcs important
        #Current order allows parent dep. trail and child (with dep. trail also as rel. parent) to be xforemd at same time w/o visual desync (child trail ctrl modifications are cancelled, which is intuitive)
        #Reverse order leads to nonintuitive double xform on child ctrls and a visual desync, requiring the trail to be snapped
        self.relative_parent_sync_dependency_matrices()
        self.apply_trail_dependency_due_parent_xformed()

        
        #optimization: todo: only recalculate drawing data if data has changed.
        op_history_len = len(context.window_manager.operators)
        #self.perspective_matrix = context.region_data.perspective_matrix
        view3D_changed = True#self.perspective_matrix == context.region_data.perspective_matrix
        value_objects_changed  =  len(updated_objects.ptr_left) > 0 or len(updated_objects.ptr_co) > 0 or len(updated_objects.ptr_right) > 0
        time_objects_changed  =  len(updated_time_objects.ptr_left) > 0 or len(updated_time_objects.ptr_co) > 0 or len(updated_time_objects.ptr_right) > 0
        any_objects_changed  =  value_objects_changed or time_objects_changed
        prev_time_objects_changed = len(prev_updated_time_objects.ptr_left) > 0 or len(prev_updated_time_objects.ptr_co) > 0 or len(prev_updated_time_objects.ptr_right) > 0
        
        can_recalculate = True
        data_changed = self.updated_active_object 
        
        frame_start,frame_end = self.frame_start,self.frame_end 
        frame_length = frame_end-frame_start  + 1

        is_current_frame_in_range = (context.scene.frame_current >= frame_start) and (context.scene.frame_current <= self.frame_end)
        
            
        ctrl_stopped_being_moved = False 
        if any_objects_changed:
            #self.steps_since_objects_was_changed=0
            #print_time('moved')
            self.delayed_snap()

            
        #self.debug_counter +=1
        #if self.debug_counter > 5:
        #    print_conditional(debug_general,'returning...')
        #    return 
        if not (view3D_changed or data_changed or any_objects_changed or prev_time_objects_changed):
            #print('render: no change, return: ' + time_string() )
            return

        #if not self.validate_trail(bpy.context):
        #    print_time('trail failed to validate, returning. Scene update.')
        #    return 
        #len_xKeys = len(self.channels_location[0].keyframe_points) if self.channels_location[0] else 0
        #len_yKeys = len(self.channels_location[1].keyframe_points) if self.channels_location[1] else 0
        #len_zKeys = len(self.channels_location[2].keyframe_points) if self.channels_location[2] else 0


        #num_keys_changed = False
        #if (len_xKeys != self.cached_len_xKeys) or (len_yKeys != self.cached_len_yKeys )or (len_zKeys != self.cached_len_zKeys):
        #    num_keys_changed=True
        #    self.cached_len_xKeys,self.cached_len_yKeys,self.cached_len_zKeys = len_xKeys,len_yKeys,len_zKeys
        #    print('key count changed..')
        #    self.ignore_control_update_once=True
        #    self.recalculate_triple_buffer(settings,force_relink=True) 
        #    self.read_sample_points()
        #    self.sync_time_ctrl_locations()
        #    return 
        #if any_objects_changed:
        #    print('render:  change' + time_string())
        #else:
        #    print('render: ctrls not changed, still rendering')
        #else:
        #    print('x:{0}|{1} y:{2}|{3} z:{4}|{5}'.format(len_xKeys,self.cached_len_xKeys,len_yKeys,self.cached_len_yKeys,len_zKeys,self.cached_len_zKeys))
        #print(time_string())
        #print(value_objects_changed)
        #sync fcurve key values
        #write key values, read from control objects
        
        if  value_objects_changed :
            #print_time('val')
            self.write_controls_to_channels()
            

            #basically, for split ctrls, otherwise not needed.
            #this recalcs the split values so that affects split ctrls are visually restricted and thus removes jitter
            #also applies to restrictive handles and channels (locked channels)
            
            #recalc handles for AUTO/CLAMPED/VECTOR to have correct values before we snap controls
            active_trail_data.recalculate_channel_handles() 
            #potential optimization: to only write control worlds for affected controls (split, restricted handles, locked)
            active_trail_data.recalculate_control_values(self.get_target_default_value())
            
            

            copy = set(self.allowed_control_update)
            self.allowed_control_update.clear()

            self.calculate_control_worlds()
            
            self.read_sample_points()
            self.sync_time_ctrl_locations()

            self.allowed_control_update = set(copy)
            


        #triplet buffer has to be reclced for correct triplet ctrl values and to do splitting.
        #however, commenting this out shows a different bug or maybe it doesnt.
        #1)Ctrl wont move with trail untiul modal finished
        #2) sometimes trail will snap back to unmoved ctrl
        #3) trail moves ahead of control if this was uncommented, i notied bfore but didn't think it was important.
        #todo: really, no need to recalc triplets at all, only need to recalc split values.
        #   because if only UI controls affected, then no new keys. No new triplets. Therefore, no new controls either. Only need to recalc split values.
        #if can_recalculate and  (not data_changed and value_objects_changed):
        #   active_trail_data.recalculate_control_values(self.get_target_default_value())
        #   self.calculate_control_worlds()
        #   #    print_time('why do i do this..? maybe for ctrl snapping when its too restrictive?')
        #   #    #print_time('--------')
        #   #    self.ignore_control_update_once=True
        #   #    self.recalculate_triple_buffer(settings) 
        #   #    can_recalculate=False
        
        #only apply retime ops if time ctrls showing.1
        #for location mode, it can only ever occur if ctrls showing
        #for rotation mode, value and time ctrls are a single ctrl. So this allows disabling retiming in the case where ctrl offsetting is used to prevent unintended retiming.
        if  settings.show_time and time_objects_changed:# or prev_time_objects_changed):
            #print_time(f'newly moved process {time_objects_changed}')
            active_trail_data.process_newly_moved_time_ctrls()
            #in scene_update, region data doesn't exist. So, gotta do this stuff within draw()
            
            

            view3D_region=None
            view3D_region_data= None  
            for window in bpy.context.window_manager.windows:
                screen = window.screen

                for area in screen.areas:
                    #print_time(area.type)
                    if area.type == 'VIEW_3D':
                        view3D_region_data = area.spaces.active.region_3d
                        #print_time(area.spaces.active.type)
                        for region in area.regions:
                            #print_time('\t' + region.type)
                            if region.type == 'WINDOW':
                                #print_time(region.type)
                                view3D_region = region
                                #print_time('succss')
                                break 
            if view3D_region and view3D_region_data:
                active_trail_data.process_moved_time_ctrls(context,view3D_region,view3D_region_data)
                active_trail_data.recalculate_channel_handles() 
                active_trail_data.recalculate_control_values(self.get_target_default_value())
                self.read_sample_points()

                
                #copy = set(self.allowed_control_update)
                #self.allowed_control_update.clear()

                self.calculate_control_worlds()
                #optimization: todo: only necessary for updated handle value objs that are Aligned and associated with moved time ctrl.
                self.sync_time_ctrl_locations()
                self.delayed_snap()
                #self.ignore_control_update_once = True
            
            
        # stalling bug might occur when scene updates and only target obj updted but no controls
        #then that means all ctrls are ignored but data_changed=TRue
        #thus we have a continuous ignore with empty allowed controls.
        #thus we have a stall.
        #which explains why hiding the target obj fixes the bug. Because then it cant update and lead to continuous empty.
        #sync data changes
        if data_changed or any_objects_changed:
            #print_time('data changed')#maybe dont ignore ctrl updates if animation playing? Updates will be frequent anyways? The ignore was to prevent circular updates anyways which doesnt matter anymore when the animation is playing.
            
            #print_time('why so many times...')


            #if not context.scene.tool_settings.use_proportional_edit_objects:
            #    self.ignore_control_update_once=True


            op_history_len = len(context.window_manager.operators)
            sel_sync = settings.selection_sync_type != 'NONE'
            if sel_sync and (not (value_objects_changed or time_objects_changed) and ((not context.screen.is_animation_playing) or (op_history_len != self.pre_op_history_len)) and (not self.ignore_time_sync_once)):
                print_conditional(debug_general,'sel sync to ctrl')
                selection_sync_time = settings.show_time and (settings.selection_sync_type =='TIME' or  not (settings.show_co or settings.show_handles))
                active_trail_data.sync_channel_sel_to_ctrls(selection_sync_time)
        #placed after processing time ctrl stuff  to avoid losing time ctrl data
        #sync key and time objects from user changes to FCurves through graph or dopesheet editors
        if  (data_changed and (not self.ignore_control_update_once) and (not any_objects_changed)):# and not (value_objects_changed and context.screen.is_animation_playing):
            #print(time_string() + 'anim playing:' + str(not (value_objects_changed and context.screen.is_animation_playing)))
            #print_conditional(debug_general or True,'data changed? but why hadnt root scene update been called?')
            
            #print('action write to controls')
            self.recalculate_triple_buffer(settings) 
            self.read_sample_points()
            self.sync_time_ctrl_locations()

        #if  any_objects_changed:
        # 
        #    active_trail_data.recalculate_channel_handles() 
        #    #placed down here so that ctrl objects snapped if handle type is restrictive (Auto,Vector)
        #    #obselete: reason: control writes to channels handles snapping already.
        #    #if can_recalculate and value_objects_changed:
        #    #print_time('why do i do this..? maybe for ctrl snapping when its too restrictive? But thats at cost of halving update rate..')
        #    ##print_time('apples')
        #    #self.ignore_control_update_once=True
        #    #self.recalculate_triple_buffer(settings) 
        #    #can_recalculate=False


        self.updated_active_object=False
        self.ignore_time_sync_once=False
        #nothing that occurs in scene_update() should set ignore flag because there's no possibility of infinite loop.
        self.ignore_control_update_once=False
        #active_trail_data.clear_updated()

        if self.is_rotation_mode():
            for objs in active_trail_data.key_objects.grouped:
                for obj in objs:
                    if not obj.select_get() and obj.empty_display_type != 'ARROWS':
                        obj.empty_display_type = 'ARROWS'
                        obj.show_x_ray = True
  
        print_conditional(debug_enable_print_func_tags,'...end process trail updates')
    


    def render(self, context):
        print_conditional(debug_enable_print_func_tags, 'start render...')
        settings = context.scene.motion_trail3D_settings
        
        render_trail = self.get_trail_info().render_trail and settings.render_trail
        if render_trail:
            gpu.state.depth_test_set('LESS_EQUAL')

            if settings.trail_use_depth:
                glDepthRange_push(0, 1)
            else:
                glDepthRange_push(0, 0)

            # Perform rendering operations
            self.render_identity(context)
            self.render_handles(context)
            self.render_time_lines(context)
            self.render_time_pts(context)
            self.render_tracking_points(context)
            self.render_nonrelative_sampled_points(context)
            self.render_relative_sampled_points(context)
            
            glDepthRange_pop()
            
            # Reset depth test and disable depth testing
            gpu.state.depth_test_set('LESS')
            gpu.state.depth_test_set('NONE')
        
            #alt coors for time sel pts
            # 50% alpha, 2 pixel width line
            '''
            gpu.state.blend_set('ALPHA')        
            shader = gpu.shader.from_builtin('UNIFORM_COLOR')
            shader.bind()
            shader.uniform_float("color", (0.0, 0.0, 0.0, 0.5))
            gpu.state.line_width_set(2)
            gpu.matrix.push()
            gpu.matrix.load_projection_matrix(self.perspective_matrix)
            gpu.matrix.pop()
            gpu.state.line_width_set(1)
            gpu.state.blend_set('NONE')
            shader.uniform_float("color", (0.0, 0.0, 0.0, 1.0))
            '''
        print_conditional(debug_enable_print_func_tags,'...end render')
        
    def render_sampled_points(self, context):
        settings = context.scene.motion_trail3D_settings
        frame_current = context.scene.frame_current - self.frame_start

        shader = gpu.shader.from_builtin('3D_UNIFORM_COLOR')
        
        # Draw lines for points up to the current frame
        color = settings.lcolor_prior_frames
        positions = self.positions
        parent_matrix_cache = self.active_parent_matrix_cache

        verts = []
        for i in range(0, min(frame_current + 1, self.length)):
            x, y, z = positions[0][i], positions[1][i], positions[2][i]
            xformed_position = parent_matrix_cache[i] @ Vector((x, y, z))
            verts.append(xformed_position)
        
        batch = batch_for_shader(shader, 'LINE_STRIP', {"pos": verts})
        shader.bind()
        shader.uniform_float("color", color)
        gpu.state.line_width_set(settings.lsize_sample)
        batch.draw(shader)

        # Draw lines for points from the current frame to the last frame
        color = settings.lcolor_post_frames
        verts = []
        for i in range(min(max(0, frame_current), self.length), self.length):
            x, y, z = positions[0][i], positions[1][i], positions[2][i]
            xformed_position = parent_matrix_cache[i] @ Vector((x, y, z))
            verts.append(xformed_position)
        
        batch = batch_for_shader(shader, 'LINE_STRIP', {"pos": verts})
        shader.bind()
        shader.uniform_float("color", color)
        batch.draw(shader)

        # Draw points for prior frames
        color = settings.ptcolor_prior_frames
        verts = []
        for i in range(0, min(frame_current + 1, self.length)):
            x, y, z = positions[0][i], positions[1][i], positions[2][i]
            xformed_position = parent_matrix_cache[i] @ Vector((x, y, z))
            verts.append(xformed_position)
        
        batch = batch_for_shader(shader, 'POINTS', {"pos": verts})
        shader.bind()
        shader.uniform_float("color", color)
        gpu.state.point_size_set(settings.ptsize_sample)
        batch.draw(shader)

        # Draw points for post frames
        color = settings.ptcolor_post_frames
        verts = []
        for i in range(min(max(0, frame_current), self.length), self.length):
            x, y, z = positions[0][i], positions[1][i], positions[2][i]
            xformed_position = parent_matrix_cache[i] @ Vector((x, y, z))
            verts.append(xformed_position)
        
        batch = batch_for_shader(shader, 'POINTS', {"pos": verts})
        shader.bind()
        shader.uniform_float("color", color)
        batch.draw(shader)

        # Reset point size to default
        gpu.state.point_size_set(1.0)


        #endregion

 
    line_shader = gpu.shader.from_builtin('UNIFORM_COLOR')
    def draw_line_strip(self,vertices,width,color):
        
        matrix = bpy.context.region_data.perspective_matrix
        line_shader =self.line_shader
        line_shader.bind()
        scale = 1.0
        func = float 
        line_shader.uniform_float('color',(func(color.r *  scale), func(color.g *  scale), func(color.b *  scale),scale))
        line_shader.uniform_float("ModelViewProjectionMatrix", matrix)
        gpu.state.line_width_set(width)
        
        batch_for_shader(line_shader,'LINE_STRIP',{"pos":vertices}).draw(line_shader)
    def draw_lines(self,vertices,width,color):
        
        matrix = bpy.context.region_data.perspective_matrix
        line_shader =self.line_shader
        line_shader.bind()
        scale = 1.0
        func = float 
        line_shader.uniform_float('color',(func(color.r *  scale), func(color.g *  scale), func(color.b *  scale), scale))
        line_shader.uniform_float("ModelViewProjectionMatrix", matrix)
        gpu.state.line_width_set(width)
        
        batch_for_shader(line_shader,'LINES',{"pos":vertices}).draw(line_shader)
    def draw_points(self, vertices, width, color):
        # Use Blender's context to get the projection matrix
        matrix = bpy.context.region_data.perspective_matrix
        line_shader = self.line_shader  # Assuming this is already initialized elsewhere

        # Bind the shader
        line_shader.bind()

        # Set the color uniform
        scale = 1.0
        func = float 
        line_shader.uniform_float('color', (func(color.r * scale), func(color.g * scale), func(color.b * scale), scale))
        
        # Set the projection matrix uniform
        line_shader.uniform_float("ModelViewProjectionMatrix", matrix)
        
        # Set the point size using the gpu module
        gpu.state.point_size_set(width)
        
        # Draw the points using batch_for_shader
        batch_for_shader(line_shader, 'POINTS', {"pos": vertices}).draw(line_shader)
        
        # Reset point size to default
        gpu.state.point_size_set(1.0)

        
    #not what i thought, inv matrix cache contains exactly whats needed
    #def extract_relative_parent_matrix(self):

    #    loc,rot,scale = self.all_control_points_root.matrix_world.decompose()

    #    #rescale to correctly place back in parent space since we removed teh scaling before.
    #    #only relevant for relative trail parenting, identity otherwise
    #    loc_scaling =self.relative_parent_inverse_matrix_cache[self.current_frame_to_index()].decompose()[2]
    #    loc[0] *= loc_scaling[0] 
    #    loc[1] *= loc_scaling[1] 
    #    loc[2] *= loc_scaling[2] 
    #    
    #    return matrix_trs(loc,rot,scale) 

    def transform_vertices(self,matrix,vertices):
            for i in range(0,len(vertices)):
                vertices[i] = matrix @ vertices[i]

    def render_identity(self,context):
        settings = context.scene.motion_trail3D_settings
        prefs = context.preferences.addons[MotionTrailPreferences.bl_idname].preferences
        #Draw lines identity lines
        #region
        if(settings.show_identity_trail):
            
            current_relative_parent_matrix = self.relative_parent_inverse_matrix_cache[self.current_frame_to_index()].inverted()

            parent_positions = self.parent_positions
            #print(parent_positions[0])
            vertices = []
            for i in range(0,self.length):
                vertices.append(parent_positions[i])
                
            self.transform_vertices(current_relative_parent_matrix,vertices)
            self.draw_line_strip(vertices,prefs.lsize_identity_path,prefs.color_identity_path)
            vertices.clear()

            #draw lines from parent curve to owner curve
            positions = self.trail_location_data.sample_values_per_channel
            parent_matrix_cache = self.active_parent_matrix_cache
            for i in range(0,self.length):
                x,y,z = positions[0][i],positions[1][i],positions[2][i]
                
                xformed_position = parent_matrix_cache[i] @ Vector((x,y,z))
                parent_position = parent_positions[i]
                
                vertices.append(xformed_position)
                vertices.append(parent_position)
            self.transform_vertices(current_relative_parent_matrix,vertices)
            self.draw_lines(vertices,prefs.lsize_identity_path,prefs.color_identity_path)
            vertices.clear()

            #line from identity curve to final position at current frame
            frame_start,frame_end = self.frame_start,self.frame_end
            is_current_frame_in_range = (context.scene.frame_current >= frame_start) and (context.scene.frame_current <= self.frame_end)

            if is_current_frame_in_range:
                i=context.scene.frame_current-frame_start
                x,y,z = positions[0][i],positions[1][i],positions[2][i]
                
                xformed_position = parent_matrix_cache[i] @ Vector((x,y,z))
                parent_position = parent_positions[i]
                
                vertices.clear()
                vertices.append(xformed_position)
                vertices.append(parent_position)
                self.transform_vertices(current_relative_parent_matrix,vertices)
                self.draw_lines(vertices,prefs.lsize_identity_path,prefs.color_identity_line)
        #endregion           
    
    def render_handles(self,context):
        settings = context.scene.motion_trail3D_settings
        prefs = context.preferences.addons[MotionTrailPreferences.bl_idname].preferences

        active_trail_data= self.active_trail_data
        triplet_buffer = active_trail_data.triplet_buffer 
        triplets_len = len(triplet_buffer)
        
        #handle lines (triplets)
        #region
        if(settings.show_handles) and (not self.is_rotation_mode()):
            
            current_relative_parent_matrix = self.relative_parent_inverse_matrix_cache[self.current_frame_to_index()].inverted()

            vertices = []
            key_objects = active_trail_data.key_objects
            for i in range(0,triplets_len):

                handle_left = Vector(key_objects.grouped[0][i].location)
                co = Vector(key_objects.grouped[1][i].location)
                handle_right =Vector(key_objects.grouped[2][i].location)

                            
                #rescale to correctly place back in parent space since we removed teh scaling before.
                #only relevant for relative trail parenting, identity otherwise
                loc_scaling =self.relative_parent_inverse_matrix_cache[i].decompose()[2]
                handle_left[0] *= loc_scaling[0] 
                handle_left[1] *= loc_scaling[1] 
                handle_left[2] *= loc_scaling[2] 

                co[0] *= loc_scaling[0] 
                co[1] *= loc_scaling[1] 
                co[2] *= loc_scaling[2] 

                handle_right[0] *= loc_scaling[0] 
                handle_right[1] *= loc_scaling[1] 
                handle_right[2] *= loc_scaling[2] 
                

                if not (obj_hide_get(key_objects.left[i])):
                    vertices.append(co)
                    vertices.append(handle_left)
                if not (obj_hide_get(key_objects.right[i])):
                    vertices.append(co)
                    vertices.append(handle_right)

            self.transform_vertices(current_relative_parent_matrix,vertices)
            self.draw_lines(vertices,prefs.lsize_handle,prefs.color_handle)

        #endregion
    def render_time_pts(self,context):
        settings = context.scene.motion_trail3D_settings
        prefs = context.preferences.addons[MotionTrailPreferences.bl_idname].preferences
        ##alternate colors for time selectable Pts so its more obvious to which co they belong to
        #region
    
        active_trail_data= self.active_trail_data
        triplet_buffer = active_trail_data.triplet_buffer 
        triplets_len = len(triplet_buffer)

        current_relative_parent_matrix = self.relative_parent_inverse_matrix_cache[self.current_frame_to_index()].inverted()

        vertices = []
        for i in range(0,triplets_len,2):
            for control_type in range(0,3):
                control_frame = round(tupled_key(active_trail_data.get_timeKey_from_triplet(i,control_type))[control_type][0])
                vertices.append(self.get_sampled_world_position(control_frame))
                
        self.transform_vertices(current_relative_parent_matrix,vertices)
        self.draw_points(vertices,prefs.ptsize_time,prefs.ptcolor_handle_timeA)

        vertices.clear()
        for i in range(1,triplets_len,2):
            for control_type in range(0,3):
                control_frame = round(tupled_key(active_trail_data.get_timeKey_from_triplet(i,control_type))[control_type][0])
                vertices.append(self.get_sampled_world_position(control_frame))
                
                
        self.transform_vertices(current_relative_parent_matrix,vertices)
        self.draw_points(vertices,prefs.ptsize_time,prefs.ptcolor_handle_timeB)

        vertices.clear()
        #for control_type,objects in enumerate(active_trail_data.updated_time_objects.grouped):
        #    for obj in objects:
        #        print('lkkl')
        #        triplet_index = obj[TAG_triplet_index]
        #        
        #        control_frame = round(tupled_key(active_trail_data.get_timeKey_from_triplet(triplet_index,control_type))[control_type][0])
        #        vertices.append(self.get_sampled_world_position(control_frame))
        #        vertices.append(obj.matrix_world.to_translation())
        #for obj_name in self.allowed_control_update:
        #    if obj_name in bpy.data.objects:

        verticesB = []
        for control_type,objects in enumerate(active_trail_data.prev_updated_time_objects.grouped):
            for obj in objects:
                triplet_index = obj[TAG_triplet_index]
                control_frame = round(tupled_key(active_trail_data.get_timeKey_from_triplet(triplet_index,control_type))[control_type][0])
                

                if triplet_index % 2 == 0:
                    vertices.append( current_relative_parent_matrix @ self.get_sampled_world_position(control_frame))
                    vertices.append(obj.matrix_world.to_translation())
                else:
                    verticesB.append( current_relative_parent_matrix @ self.get_sampled_world_position(control_frame))
                    verticesB.append(obj.matrix_world.to_translation())
        
        self.draw_lines(vertices,max(1,prefs.lsize_time/2),prefs.lcolor_handle_timeA)
        self.draw_lines(verticesB,max(1,prefs.lsize_time/2),prefs.lcolor_handle_timeB)

        #endregion      
    def render_time_lines(self,context):
        settings = context.scene.motion_trail3D_settings
        prefs = context.preferences.addons[MotionTrailPreferences.bl_idname].preferences

        active_trail_data= self.active_trail_data
        triplet_buffer = active_trail_data.triplet_buffer 
        triplets_len = len(triplet_buffer)
        current_relative_parent_matrix = self.relative_parent_inverse_matrix_cache[self.current_frame_to_index()].inverted()

        #alternate colors for time selectable so its more obvious to which co they belong to
        #region

        channels = active_trail_data.channels
        vertices = []
        #alternate colors for time selectable so its more obvious to which co they belong to
        for i in range(0,triplets_len,2):
            
            triplet = triplet_buffer[i]

            time_axis = triplet.time_axes[0]
            handle_keyindex = triplet[time_axis]
            handle_channel = channels[time_axis]
            left_handle_frame = round(handle_channel.keyframe_points[handle_keyindex].handle_left[0])

            time_axis = triplet.time_axes[2]
            handle_keyindex = triplet[time_axis]
            handle_channel = channels[time_axis]
            right_handle_frame = round(handle_channel.keyframe_points[handle_keyindex].handle_right[0])

            for frame in range(left_handle_frame,right_handle_frame):
                vertices.append(self.get_sampled_world_position(frame))
                vertices.append(self.get_sampled_world_position(frame+1))
                
        self.transform_vertices(current_relative_parent_matrix,vertices)
        self.draw_lines(vertices,prefs.lsize_time,prefs.lcolor_handle_timeA)

        vertices.clear()
        #alternate colors for time selectable Lines so its more obvious to which co they belong to
        for i in range(1,triplets_len,2):
            triplet = triplet_buffer[i]

            time_axis = triplet.time_axes[0]
            left_handle_frame = round(channels[time_axis].keyframe_points[triplet[time_axis]].handle_left[0])
            time_axis = triplet.time_axes[2]
            right_handle_frame = round(channels[time_axis].keyframe_points[triplet[time_axis]].handle_right[0])
            for frame in range(left_handle_frame,right_handle_frame):
                vertices.append(self.get_sampled_world_position(frame))
                vertices.append(self.get_sampled_world_position(frame+1))
                
        self.transform_vertices(current_relative_parent_matrix,vertices)
        self.draw_lines(vertices,prefs.lsize_time,prefs.lcolor_handle_timeB)
        
        #endregion    
    def render_relative_sampled_points(self,context):
        settings = context.scene.motion_trail3D_settings
        prefs = context.preferences.addons[MotionTrailPreferences.bl_idname].preferences
        active_trail_data= self.active_trail_data
        triplet_buffer = active_trail_data.triplet_buffer 
        triplets_len = len(triplet_buffer)
        #sampled points
        #region
        #points up to current frame
        frame_current = context.scene.frame_current - self.frame_start
        current_relative_parent_matrix = self.relative_parent_inverse_matrix_cache[self.current_frame_to_index()].inverted()
        
        vertices = []
        positions = self.trail_location_data.sample_values_per_channel
        parent_matrix_cache = self.active_parent_matrix_cache
        for i in range(0,min(frame_current+1,self.length)):
            x,y,z = positions[0][i],positions[1][i],positions[2][i]
            
            xformed_position = parent_matrix_cache[i] @ Vector((x,y,z))
            vertices.append(xformed_position)
            
        self.transform_vertices(current_relative_parent_matrix,vertices)
        self.draw_line_strip(vertices,prefs.lsize_sample,prefs.lcolor_prior_frames)
        
        #points from current frame to last frame
        vertices.clear()
        for i in range(min(max(0,frame_current),self.length),self.length):
            x,y,z = positions[0][i],positions[1][i],positions[2][i]
            
            xformed_position = parent_matrix_cache[i] @ Vector((x,y,z))
            vertices.append(xformed_position)

        self.transform_vertices(current_relative_parent_matrix,vertices)
        self.draw_line_strip(vertices,prefs.lsize_sample,prefs.lcolor_post_frames)
            

        vertices.clear()
        for i in range(0,min(frame_current+1,self.length)):
            x,y,z = positions[0][i],positions[1][i],positions[2][i]
            
            xformed_position = parent_matrix_cache[i] @ Vector((x,y,z))
            vertices.append(xformed_position)

        self.transform_vertices(current_relative_parent_matrix,vertices)
        self.draw_points(vertices,prefs.ptsize_sample,prefs.ptcolor_prior_frames)
        
        vertices.clear()
        for i in range(min(max(0,frame_current),self.length),self.length):
            x,y,z = positions[0][i],positions[1][i],positions[2][i]
            
            xformed_position = parent_matrix_cache[i] @ Vector((x,y,z))
            vertices.append(xformed_position)

        self.transform_vertices(current_relative_parent_matrix,vertices)
        self.draw_points(vertices,prefs.ptsize_sample,prefs.ptcolor_post_frames)
        
        #endregion 
    def render_tracking_points(self,context):
        #Q:why do I calculate target position using active matrix instead of tracker matrix @ vec_zero?
        settings = context.scene.motion_trail3D_settings
        prefs = context.preferences.addons[MotionTrailPreferences.bl_idname].preferences
        
        active_trail_data= self.active_trail_data
        triplet_buffer = active_trail_data.triplet_buffer 
        triplets_len = len(triplet_buffer)
        frame_start,frame_end = self.frame_start,self.frame_end
        frame_length = frame_end-frame_start  + 1
        frame_current = context.scene.frame_current - frame_start
        is_current_frame_in_range = (context.scene.frame_current >= frame_start) and (context.scene.frame_current <= self.frame_end)

        current_relative_parent_matrix = self.relative_parent_inverse_matrix_cache[self.current_frame_to_index()].inverted()
        

        #tracking points
        #region
        if settings.show_tracking:
            frame_start,frame_end = self.frame_start,self.frame_end 
            frame_length = frame_end-frame_start  + 1
            tracking_infos = self.target.motion_trail3D.tracking_points

            if settings.tracker_use_depth:
                glDepthRange_push(0,1)
            else:
                glDepthRange_push(0,0)


            tracking_infos = tracking_infos[:]
            trailOp = self.get_trail_info()
            dependency_tracking_info = None 
            for i in reversed(range(0,len(tracking_infos))):
                tracking_info = tracking_infos[i]

                if tracking_info.show_tracking:
                    #use single general name instead of specific since the use is less about the specific target and more about the owner and having a tracker.
                    if tracking_info.name == '_dependency_': #trailOp.dependency.target_name:
                        dependency_tracking_info = tracking_info
                        del tracking_infos[i] 
                        break 
                #don't render hidden tracker trail unless it's the current control offset trail.
                elif tracking_info.name != trailOp.control_offset_tracker_name:
                    del tracking_infos[i]

            vertices = []   
            for tracking_info in tracking_infos:
                if tracking_info.show_continuous:
                    
                    vertices.clear()
                    for frame_index in range(0,min(frame_current+1,self.length)):
                        parent_matrix = self.tracking_identity_matrices[frame_index]
                        position = parent_matrix @ tracking_info.get_location()
                        vertices.append(position)

                    self.transform_vertices(current_relative_parent_matrix,vertices)
                    self.draw_line_strip(vertices,tracking_info.lsize_tracking,tracking_info.lcolor_tracking_prior)
                    
                    vertices.clear()
                    for frame_index in range(min(max(0,frame_current),self.length),self.length):
                        parent_matrix = self.tracking_identity_matrices[frame_index]
                        position = parent_matrix @ tracking_info.get_location()
                        vertices.append(position)
                        
                    self.transform_vertices(current_relative_parent_matrix,vertices)
                    self.draw_line_strip(vertices,tracking_info.lsize_tracking,tracking_info.lcolor_tracking_post)

            positions = self.trail_location_data.sample_values_per_channel
            for tracking_info in tracking_infos:
                if tracking_info.show_lines_from_target:
                    
                    vertices.clear()
                    for frame_index in range(0,min(frame_current+1,self.length)):
                        tracker_parent_matrix = self.tracking_identity_matrices[frame_index]
                        target_parent_matrix = self.active_parent_matrix_cache[frame_index]
                        position = tracker_parent_matrix @ tracking_info.get_location()
                        targetPosition =target_parent_matrix @ Vector((positions[0][frame_index],positions[1][frame_index],positions[2][frame_index]))

                        vertices.append(targetPosition)
                        vertices.append(position)
                    self.transform_vertices(current_relative_parent_matrix,vertices)
                    self.draw_lines(vertices,tracking_info.lsize_tracking,tracking_info.lcolor_tracking_prior)

                    vertices.clear()
                    for frame_index in range(min(max(0,frame_current),self.length),self.length):
                        tracker_parent_matrix = self.tracking_identity_matrices[frame_index]
                        target_parent_matrix = self.active_parent_matrix_cache[frame_index]
                        position = tracker_parent_matrix @ tracking_info.get_location()
                        targetPosition =target_parent_matrix @ Vector((positions[0][frame_index],positions[1][frame_index],positions[2][frame_index]))

                        vertices.append(targetPosition)
                        vertices.append(position)
                    self.transform_vertices(current_relative_parent_matrix,vertices)
                    self.draw_lines(vertices,tracking_info.lsize_tracking,tracking_info.lcolor_tracking_post)

            for tracking_info in tracking_infos:
                vertices.clear()
                for frame_index in range(0,min(frame_current+1,self.length)):
                    parent_matrix = self.tracking_identity_matrices[frame_index]
                    position = parent_matrix @ tracking_info.get_location()
                    vertices.append(position)
                self.transform_vertices(current_relative_parent_matrix,vertices)
                self.draw_points(vertices,tracking_info.ptsize_tracking,tracking_info.ptcolor_tracking_prior)
                
                vertices.clear()
                for frame_index in range(min(max(0,frame_current),self.length),self.length):
                    parent_matrix = self.tracking_identity_matrices[frame_index]
                    position = parent_matrix @ tracking_info.get_location()
                    vertices.append(position)
                self.transform_vertices(current_relative_parent_matrix,vertices)
                self.draw_points(vertices,tracking_info.ptsize_tracking,tracking_info.ptcolor_tracking_post)

            
            frame_index = context.scene.frame_current -  frame_start
            if frame_index >= 0 and frame_index < frame_length:
                for tracking_info in tracking_infos:
                    parent_matrix = self.tracking_identity_matrices[frame_index]
                    position = parent_matrix @ tracking_info.get_location()

                    vertices.clear()
                    vertices.append(position)

                    self.transform_vertices(current_relative_parent_matrix,vertices)
                    self.draw_points(vertices,tracking_info.ptsize_tracking,tracking_info.color_tracking_active)
                
                for tracking_info in tracking_infos:
                    if tracking_info.show_lines_from_target:
                        
                        tracker_parent_matrix = self.tracking_identity_matrices[frame_index]
                        target_parent_matrix = self.active_parent_matrix_cache[frame_index]
                        position = tracker_parent_matrix @ tracking_info.get_location()
                        targetPosition =target_parent_matrix @ Vector((positions[0][frame_index],positions[1][frame_index],positions[2][frame_index]))

                        vertices.clear()
                        vertices.append(targetPosition)
                        vertices.append(position)

                        self.transform_vertices(current_relative_parent_matrix,vertices)
                        self.draw_lines(vertices,prefs.lsize_tracking_active,tracking_info.color_tracking_active)
                        
            if self.dependency_target_is_valid and dependency_tracking_info != None:
                tracking_info = dependency_tracking_info
                
                valid_dependency_targets = {trail.target_name:trail for trail in settings.active_trails}
                info = trailOp.dependency
                target_trail = valid_dependency_targets[info.target_name]
                child_dependency_matrices = target_trail.child_dependency_matrices

                if tracking_info.show_continuous:
                    
                    vertices.clear()
                    for frame_index in range(0,min(frame_current+1,self.length)):
                        parent_matrix = self.tracking_identity_matrices[frame_index]

                        position =  parent_matrix @ tracking_info.get_location()
                        vertices.append(position)

                    self.transform_vertices(current_relative_parent_matrix,vertices)
                    self.draw_line_strip(vertices,tracking_info.lsize_tracking,tracking_info.lcolor_tracking_prior)
                    
                    vertices.clear()
                    for frame_index in range(min(max(0,frame_current),self.length),self.length):
                        parent_matrix = self.tracking_identity_matrices[frame_index]
                        position = parent_matrix @ tracking_info.get_location()
                        vertices.append(position)
                        
                    self.transform_vertices(current_relative_parent_matrix,vertices)
                    self.draw_line_strip(vertices,tracking_info.lsize_tracking,tracking_info.lcolor_tracking_post)
                
                if tracking_info.show_lines_from_target:
                    vertices.clear()
                    for frame_index in range(0,min(frame_current+1,self.length)):
                        tracker_parent_matrix = self.tracking_identity_matrices[frame_index]
                        target_parent_matrix = self.relative_parent_inverse_matrix_cache[frame_index] @ child_dependency_matrices[frame_index].get() 


                        position = tracker_parent_matrix @ tracking_info.get_location()
                        targetPosition =target_parent_matrix @ Vector((0,0,0))

                        vertices.append(targetPosition)
                        vertices.append(position)
                    self.transform_vertices(current_relative_parent_matrix,vertices)
                    self.draw_lines(vertices,tracking_info.lsize_tracking,tracking_info.lcolor_tracking_prior)

                    vertices.clear()
                    for frame_index in range(min(max(0,frame_current),self.length),self.length):
                        tracker_parent_matrix = self.tracking_identity_matrices[frame_index]
                        target_parent_matrix = self.relative_parent_inverse_matrix_cache[frame_index] @ child_dependency_matrices[frame_index].get()
                        position = tracker_parent_matrix @ tracking_info.get_location()
                        targetPosition =target_parent_matrix @ Vector((0,0,0))

                        vertices.append(targetPosition)
                        vertices.append(position)
                    self.transform_vertices(current_relative_parent_matrix,vertices)
                    self.draw_lines(vertices,tracking_info.lsize_tracking,tracking_info.lcolor_tracking_post)

                vertices.clear()
                for frame_index in range(0,min(frame_current+1,self.length)):
                    parent_matrix = self.tracking_identity_matrices[frame_index]
                    position = parent_matrix @ tracking_info.get_location()
                    vertices.append(position)
                self.transform_vertices(current_relative_parent_matrix,vertices)
                self.draw_points(vertices,tracking_info.ptsize_tracking,tracking_info.ptcolor_tracking_prior)
                
                vertices.clear()
                for frame_index in range(min(max(0,frame_current),self.length),self.length):
                    parent_matrix = self.tracking_identity_matrices[frame_index]
                    position = parent_matrix @ tracking_info.get_location()
                    vertices.append(position)
                self.transform_vertices(current_relative_parent_matrix,vertices)
                self.draw_points(vertices,tracking_info.ptsize_tracking,tracking_info.ptcolor_tracking_post)

            
                frame_index = context.scene.frame_current -  frame_start
                if frame_index >= 0 and frame_index < frame_length:
                    parent_matrix = self.tracking_identity_matrices[frame_index]
                    position = parent_matrix @ tracking_info.get_location()

                    vertices.clear()
                    vertices.append(position)

                    self.transform_vertices(current_relative_parent_matrix,vertices)
                    self.draw_points(vertices,tracking_info.ptsize_tracking,tracking_info.color_tracking_active)

                    if tracking_info.show_lines_from_target:
                            
                        tracker_parent_matrix = self.tracking_identity_matrices[frame_index]
                        target_parent_matrix = self.relative_parent_inverse_matrix_cache[frame_index] @ child_dependency_matrices[frame_index].get()
                        position = tracker_parent_matrix @ tracking_info.get_location()
                        targetPosition =target_parent_matrix @ Vector((0,0,0))

                        vertices.clear()
                        vertices.append(targetPosition)
                        vertices.append(position)

                        self.transform_vertices(current_relative_parent_matrix,vertices)
                        self.draw_lines(vertices,prefs.lsize_tracking_active,tracking_info.color_tracking_active)
        
            glDepthRange_pop()

        #endregion
    def render_nonrelative_sampled_points(self,context):
        settings = context.scene.motion_trail3D_settings

        if settings.enable_relative_parent and settings.relative_parent_render_world and self.relative_parent_is_valid:
            prefs = context.preferences.addons[MotionTrailPreferences.bl_idname].preferences
            active_trail_data= self.active_trail_data
            triplet_buffer = active_trail_data.triplet_buffer 
            triplets_len = len(triplet_buffer)
            #sampled points
            #region
            #points up to current frame

            frame_current = context.scene.frame_current - self.frame_start
            
            vertices = []
            positions = self.trail_location_data.sample_values_per_channel
            active_parent_matrix_cache = self.nonrelative_parent_matrix_cache
            
            
            for i in range(0,min(frame_current+1,self.length)):
                x,y,z = positions[0][i],positions[1][i],positions[2][i]
                
                xformed_position = active_parent_matrix_cache[i] @ Vector((x,y,z))
                vertices.append(xformed_position)

            self.draw_line_strip(vertices,prefs.lsize_sample,prefs.lcolor_prior_frames)
            vertices.clear()

            #points from current frame to last frame
            positions = self.trail_location_data.sample_values_per_channel
            for i in range(min(max(0,frame_current),self.length),self.length):
                x,y,z = positions[0][i],positions[1][i],positions[2][i]
                
                xformed_position = active_parent_matrix_cache[i] @ Vector((x,y,z))
                vertices.append(xformed_position)
            
            self.draw_line_strip(vertices,prefs.lsize_sample,prefs.lcolor_post_frames)
            vertices.clear()

            positions = self.trail_location_data.sample_values_per_channel
            active_parent_matrix_cache = self.nonrelative_parent_matrix_cache
            for i in range(0,min(frame_current+1,self.length)):
                x,y,z = positions[0][i],positions[1][i],positions[2][i]
                
                xformed_position = active_parent_matrix_cache[i] @ Vector((x,y,z))
                vertices.append(xformed_position)

            self.draw_points(vertices,prefs.ptsize_sample,prefs.ptcolor_prior_frames)
            vertices.clear()
            
            for i in range(min(max(0,frame_current),self.length),self.length):
                x,y,z = positions[0][i],positions[1][i],positions[2][i]
                
                xformed_position = active_parent_matrix_cache[i] @ Vector((x,y,z))
                vertices.append(xformed_position)
            self.draw_points(vertices,prefs.ptsize_sample,prefs.ptcolor_post_frames)
            vertices.clear()
    def read_sample_points(self):
        #print_time('intersting')
        #draw called often. This allows user's changes to be seen quickly
        #using channel.evaluate also takes into account fcurve modifiers.
        #modal op not called during other Blender ops (grapheditor keyframe dragging)
        #if animation playing then modal op will be called during op.
        frame_start,frame_end = self.frame_start,self.frame_end
        #sync positions 
        self.trail_location_data.read_sample_points(self.target.location)

        if self.is_rotation_mode():
            self.active_trail_data.read_sample_points(self.get_target_default_value())
            
        #calculate target basis matrices
        default_location = self.target.location.copy()
        default_rotation = self.target_rotations[self.target.rotation_mode]#list of rotations per mode 
        default_scale = self.target.scale.copy()
        rotation_mode = self.target.rotation_mode 
        rot_build_func = self.rotation_build_funcs[rotation_mode]
        
        info = self.get_trail_info()
        #print('a')
        child_dependency_matrices = info.child_dependency_matrices

        #print('b')
        #print('channels not derefeD? ')
        #print(str(self.channels_location))

        for i in range(frame_start,frame_end+1):
            index = i - frame_start
            
            #print('c')
            basis_location = default_location
            for channel_index,channel in enumerate(self.channels_location):
                if channel:
                    basis_location[channel_index] = channel.evaluate(frame=i)

            basis_scale = default_scale
            for channel_index,channel in enumerate(self.channels_scale):
                if channel:
                    basis_scale[channel_index] = channel.evaluate(frame=i)

            basis_rotation = default_rotation
            for channel_index, channel in enumerate(self.channels_rotation[rotation_mode]):
                if channel:
                    basis_rotation[channel_index] = channel.evaluate(frame=i)

            #print('e')
            basis = Matrix.Translation(Vector(basis_location)) @  rot_build_func(basis_rotation) @ matrix_scale(basis_scale)
            
            self.tracking_identity_matrices[index] = self.active_parent_matrix_cache[index] @ basis
            #we don't use active cache to allow dependency trail to use its own parent 
            #premul rel matrix to avoid double applying it
            child_dependency_matrices[index].set_matrix( self.relative_parent_inverse_matrix_cache[index].inverted() @self.active_parent_matrix_cache[index] @ basis)

        #print('d?')
    def sync_time_ctrl_locations(self):
        '''[mode-generalized], moves mode's time ctrl onto world-space location sample points'''
        active_trail_data = self.active_trail_data
        key_time_objects = active_trail_data.key_time_objects
        prev_updated_time_objects = active_trail_data.prev_updated_time_objects
        
        frame_start,frame_end = self.frame_start,self.frame_end
        #todo:[1/14/20] apply ctrl offset to time ctrls too... can't do at this time since get_sampled_wrold pos only samples location dawta, not the additional local rotation. Not needed for general testing purposes yet though
        control_offset = self.get_control_offset_matrix()

        for control_type,objects in enumerate(key_time_objects.grouped): 
            for triplet_index,obj in enumerate(objects):
                if (obj not in prev_updated_time_objects[control_type]):
                    if obj.name not in self.allowed_control_update:
                        triplet_index = obj[TAG_triplet_index]
                        raw_frame = tupled_key(active_trail_data.get_timeKey_from_triplet(triplet_index,control_type))[control_type][0]
                        frame = round(raw_frame)



                        matrix_index = clamp(frame,frame_start,frame_end) - frame_start
                        world_position = (self.tracking_identity_matrices[matrix_index] @ control_offset).decompose()[0]
                        
                        loc_scaling =self.relative_parent_inverse_matrix_cache[matrix_index].inverted().decompose()[2]
                        #for some reason trls are not even being calc wright even without relative parenting . whats oging on?
                        world_position[0] *= loc_scaling[0] 
                        world_position[1] *= loc_scaling[1] 
                        world_position[2] *= loc_scaling[2] 

                        #world_position = self.get_sampled_world_position(frame)

                        obj.location = world_position
                    #else:
                    #    print_time('did not time sync: ' + obj.name)

    def modal(self,context,event):
        
        if crash_stop_everything:
            print_time('CSE modal')
            return 
            
            
        print_conditional(debug_enable_print_func_tags or debug_crash_search  ,'modal...')
        if not self.ERROR_motion_trail:
            try:
                result =  self.trail_update(context,event)
                print_conditional(debug_enable_print_func_tags or debug_crash_search,'..end modal')
                return result 
            except Exception as e:
                self.ERROR_motion_trail=True
                #print(e)
                import traceback
                msg = traceback.format_exc()
                self.report(type={'ERROR'},message=msg)
                print_time('[ERROR] : ' + msg)
                return {'FINISHED'}
        
        if self.ERROR_motion_trail and not self.is_disposed:
            print_time('diposing trail due to error.')
            context.area.tag_redraw()
            self.dispose()
            return {'FINISHED'}
            



    def trail_update(self, context, event):

        settings = context.scene.motion_trail3D_settings


        if not self.is_active_get() or (context.region is None):
            #(context.region is None): attempt to save? end the trail
            print_time('not active, returning. Modal.')
            if context.region is None:
                print_time('lost window.')
            if not self.is_disposed:
                print_time('possible undo detected past trail init or window lost. Disposing motion trail. Modal')
                self.dispose()
            #consider:returning cancelled won't insert an undo op if user undo passed trail init. Might be useful?
            return {'FINISHED'}

        self.increment_undo_tracker() 

        #tiny efficiency thing.. if trail hidden, no need for it to do any processing..
        render_trail = self.get_trail_info().render_trail  and  settings.render_trail
        if not render_trail:
            return {'PASS_THROUGH'}

        if not self.validate_trail(context):
            return {'PASS_THROUGH'}


        '''
        when other ops are active, this modal isn't called, unless the animation is playing.
        ex: when user dragging key handles in graph editor, any data updates here to sync the draw wont occur till after the op is finished
        '''

        
        if(self.apply_trail_dependency_flags_change()):
            return {'PASS_THROUGH'}
        if self.relative_parent_check_flags_change(): 
            return {'PASS_THROUGH'}
            
        
        should_cancel = (self.frame_start !=  context.scene.frame_preview_start) or (self.frame_end != context.scene.frame_preview_end)
        #should_cancel = should_cancel or (event.type == 'Z' and event.value == 'PRESS' and event.ctrl)  #undo pressed
        #action may change due to all keys being deleted then inserting new keys...
        action_changed = self.active_object.animation_data is None or self.active_object.animation_data.action != self.action

        if should_cancel or action_changed:
            if action_changed:
                print_time('action changed. Trail disposed.')
            context.area.tag_redraw()
            self.dispose()
            return {'FINISHED'}
        
        active_object = context.active_object 
        #if (active_object is not None) and (TAG_triplet_index in active_object):
        #    context.area.header_text_set(active_object['trail_tag'])      

        trailOp = self.get_trail_info()
        if trailOp.refresh:
            #todo: reapply relative parent cache/dep. cache
            trailOp.refresh = False 
            #these will re-eval next frame
            self.apply_trail_dependency_flags_change(True)
            self.relative_parent_check_flags_change(True)

            if not( self.dependency_target_is_valid or self.relative_parent_is_valid):
                self.ignore_control_update_once=True 
                self.calculate_parent_matrix_cache()
                self.recalculate_triple_buffer(settings,force_relink=True)
                #ensure drawn sample points update, mostly so it doesn't appear to be bugged.
                #without this, the ctrl obj would be correctly placed but the trail rendered point wouldn't have been updated yet.
                self.read_sample_points()
                self.sync_time_ctrl_locations()
                    
            self.report({'INFO'},'Refreshed Trail ' + self.target_name)
            return {'PASS_THROUGH'}

        op_history_len = len(context.window_manager.operators)
        op_finished = op_history_len != self.pre_op_history_len
        self.pre_op_history_len = op_history_len 
        
        event_used = False
        mouse_position = Vector((event.mouse_region_x, event.mouse_region_y))
        region_width,region_height = context.region.width,context.region.height
        #mouse out of region
        if mouse_position.x < 0 or mouse_position.x > region_width or mouse_position.y<0 or mouse_position.y > region_height:
            return {'PASS_THROUGH'}



        #this modal func is called again after an op (like translating a time object) finishes, probably due to the events raised (mouse clicks, keys presses)
        #If user translated a control object, then render() will fill the prev_updated_objects.
        #While the translation op is active, this modal() isn't called. Therefore, when it finally is, clear the prev_update_objects buffer,
        #since we know that the user isn't operating in the 3D view anymore.
        #caveat: modal called if animation is playing, even if a differnt op is executing
        active_trail_data = self.active_trail_data
        prev_updated_time_objects = active_trail_data.prev_updated_time_objects
        key_time_objects = active_trail_data.key_time_objects
        prev_time_objects_changed = len(prev_updated_time_objects.left) > 0 or len(prev_updated_time_objects.co) > 0 or len(prev_updated_time_objects.right) > 0

        if  not context.screen.is_animation_playing or op_finished:
            prev_updated_time_objects.clear()

            #move time objects onto motion trail
            if prev_time_objects_changed:
                print_conditional(debug_general,'op finished')
                context.area.tag_redraw()
                self.ignore_control_update_once=True
                self.sync_time_ctrl_locations()

        #if not event_used and event.type in {'ESC'} and event.value == 'RELEASE':
        #    context.area.tag_redraw()
        #    self.dispose()
        #    return {'FINISHED'}

        if profile and not event_used and event.type in {'Q'} and event.value == 'PRESS':
            event_used=True
            print_profiler_functions(self.profiler_items,self.parent_calls,'')

        #toggle trail mode
        #if not event_used and event.type in {'TAB'} and event.value == 'PRESS':
        #    event_used=True
        #    settings.trail_mode = 'LOCATION' if settings.trail_mode == 'ROTATION' else 'ROTATION'

        #can return PASS_THROUGH to allow all other UI to work. No need for updating on scene_update callback
        if not event_used:
            return {'PASS_THROUGH'}
        else:
            return {'RUNNING_MODAL'}
        #print('end trail update')
    
    
    def write_controls_to_channels(self):
        
        #print_time('write ctrls to channels')
        #optimization: (though user only ever updates less than 10 objs at a time, soo not really necessary.. but) reorder loops so axis is the outter most so lock check occurs only 3 times total instead of 3*len(total updated objects)
        active_trail_data = self.active_trail_data
        channels = active_trail_data.channels
        triplet_buffer =active_trail_data.triplet_buffer
        updated_objects = active_trail_data.updated_objects
        parent_matrix_cache = self.active_parent_matrix_cache
        
        control_locals = active_trail_data.key_values_per_channel

        #inv only needs to be applied in location mode, otherwise doesn't affect rotation control writes
        control_offset_inv = Matrix.Identity(4)
        trailOp = self.get_trail_info()
        if len(trailOp.control_offset_tracker_name) > 0:
            tracking_points = self.target.motion_trail3D.tracking_points 
            for tracker in tracking_points:
                if tracker.name == trailOp.control_offset_tracker_name:
                    control_offset_inv = Matrix.Translation(tracker.get_location()).inverted()

        if not self.is_rotation_mode():
            for updated_object in updated_objects.left:
                triplet_index = updated_object[TAG_triplet_index]
                triplet = triplet_buffer[triplet_index]
                
                matrix_index =active_trail_data.get_triplet_frame_index(triplet_index,0)
                parent_matrix =  parent_matrix_cache[matrix_index] 

                loc = updated_object.matrix_basis.decompose()[0]
                
                #rescale to correctly place back in parent space since we removed teh scaling before.
                #only relevant for relative trail parenting, identity otherwise
                loc_scaling =self.relative_parent_inverse_matrix_cache[matrix_index].decompose()[2]
                loc[0] *= loc_scaling[0] 
                loc[1] *= loc_scaling[1] 
                loc[2] *= loc_scaling[2] 
                
                _,rot,scale = self.tracking_identity_matrices[matrix_index].decompose()
                matrix_basis = matrix_trs(loc,rot,scale)

                #position_local = (parent_matrix.inverted() @ updated_object.matrix_basis).to_translation()
                position_local = (parent_matrix.inverted() @ matrix_basis @ control_offset_inv).to_translation()

                for axis in range(0,3):
                    if ((triplet[axis]  is not None )and  not channels[axis].lock) :
                        key = channels[axis].keyframe_points[triplet.indices[axis]]

                        if is_handle_type_editable(key.handle_left_type):
                            key.handle_left =(key.handle_left[0],position_local[axis])
                            #update locals .. but might as well recalc control values or whole triplet buffer due to affected splits..
                            #control_locals[axis][triplet_index][0] = key.handle_left[1]

                            if not active_trail_data.key_objects[2][triplet_index].select_get():
                                align_right_handle(key)
                            
            #root = self.all_control_points_root
            for updated_object in  updated_objects.co:
                #print_time('updated' )
                triplet_index = updated_object[TAG_triplet_index]
                triplet = triplet_buffer[triplet_index]

                matrix_index =active_trail_data.get_triplet_frame_index(triplet_index,1)
                parent_matrix =  parent_matrix_cache[matrix_index]

                #if i use world.. then consrtaints would be taken into account?-yep
                #not  enough support yet for constrained trail so just commented out for now.
                #loc = (root.matrix_world.inverted() @  updated_object.matrix_world).decompose()[0]
                loc = updated_object.matrix_basis.decompose()[0]
                
                #rescale to correctly place back in parent space since we removed teh scaling before.
                #only relevant for relative trail parenting, identity otherwise
                loc_scaling =self.relative_parent_inverse_matrix_cache[matrix_index].decompose()[2]
                loc[0] *= loc_scaling[0] 
                loc[1] *= loc_scaling[1] 
                loc[2] *= loc_scaling[2] 
                
                _,rot,scale = self.tracking_identity_matrices[matrix_index].decompose()
                matrix_basis = matrix_trs(loc,rot,scale)

                #position_local = (parent_matrix.inverted() @ updated_object.matrix_basis).to_translation()
                position_local = (parent_matrix.inverted() @ matrix_basis @ control_offset_inv).to_translation()


                for axis in range(0,3):
                    if ((triplet[axis] is not None) and not channels[axis].lock):
                        key = channels[axis].keyframe_points[triplet.indices[axis]]

                        co_offset = position_local[axis] - key.co[1]
                        
                        if not active_trail_data.key_objects[0][triplet_index].select_get():
                            offset_left_handle(key,co_offset)

                        if not active_trail_data.key_objects[2][triplet_index].select_get():
                            offset_right_handle(key,co_offset)

                        #return
                        #....why does writing to a key co lock xform of unrelatedb ones...
                        key.co =(key.co[0],position_local[axis])
                        #update locals .. but might as well recalc control values or whole triplet buffer due to affected splits..
                        #control_locals[axis][triplet_index][1] = key.co[1]

            for updated_object in  updated_objects.right:
                triplet_index = updated_object[TAG_triplet_index]
                triplet = triplet_buffer[triplet_index]
                
                matrix_index =active_trail_data.get_triplet_frame_index(triplet_index,2)
                parent_matrix =  parent_matrix_cache[matrix_index]

                loc = updated_object.matrix_basis.decompose()[0]
                
                #rescale to correctly place back in parent space since we removed teh scaling before.
                #only relevant for relative trail parenting, identity otherwise
                loc_scaling =self.relative_parent_inverse_matrix_cache[matrix_index].decompose()[2]
                loc[0] *= loc_scaling[0] 
                loc[1] *= loc_scaling[1] 
                loc[2] *= loc_scaling[2] 
                
                _,rot,scale = self.tracking_identity_matrices[matrix_index].decompose()
                matrix_basis = matrix_trs(loc,rot,scale)

                #position_local = (parent_matrix.inverted() @ updated_object.matrix_basis).to_translation()
                position_local = (parent_matrix.inverted() @ matrix_basis @ control_offset_inv).to_translation()


                for axis in range(0,3):
                    if ((triplet[axis]  is not None) and not channels[axis].lock):
                        key = channels[axis].keyframe_points[triplet.indices[axis]]

                        if is_handle_type_editable(key.handle_right_type):
                            key.handle_right =(key.handle_right[0],position_local[axis])
                            if not active_trail_data.key_objects[0][triplet_index].select_get():
                                align_left_handle(key)
                                #control_locals[axis][triplet_index][0] = key.handle_left[1]
                            #update locals .. but might as well recalc control values or whole triplet buffer due to affected splits..
                            #control_locals[axis][triplet_index][2] = key.handle_right[1]

            key_objects = active_trail_data.key_objects
            control_locals = active_trail_data.key_values_per_channel
            parent_matrix_cache = self.active_parent_matrix_cache  
            control_offset = self.get_control_offset_matrix()
            
            if False:
                #For restricted handles, snap them despite being updated by user.
                for updated_object in updated_objects.left:
                    triplet_index = updated_object[TAG_triplet_index]
                    triplet = triplet_buffer[triplet_index]
                    
                    any_axis_restrictive = False
                    for axis in range(0,3):
                        any_axis_restrictive = any_axis_restrictive  or (triplet[axis] is None ) or channels[axis].lock or (not is_handle_type_editable(channels[axis].keyframe_points[triplet.indices[axis]].handle_left_type))
                    if any_axis_restrictive:
                        
                        #print('restrictive left')
                        control_type = 0
                        i = triplet_index
                        ctrl_object = key_objects.grouped[control_type][i]

                        local = Vector((control_locals[0][i][control_type],control_locals[1][i][control_type],control_locals[2][i][control_type]))
                        matrix_index = active_trail_data.get_triplet_frame_index(i,control_type)
                        parent_matrix =  parent_matrix_cache[matrix_index]
                        world = parent_matrix @ local

                        channel_basis = parent_matrix.inverted() @ self.tracking_identity_matrices[matrix_index]
                        _,rot,scale = channel_basis.decompose()
                        channel_basis = matrix_trs(Vector(),rot,scale)#remove location from basis since controls have a defined location
                        world = (parent_matrix @ Matrix.Translation(local) @ channel_basis @ control_offset).decompose()[0]
                        

                        ctrl_object.scale = (1,1,1)
                        ctrl_object.location = world
                        ctrl_object.rotation_quaternion = parent_matrix.to_quaternion()

                        #removing from buffer means, for whatever reason, that the snap will be jittery.  
                        #otherwise, its butter smooth for restricting control to given axis.
                        #self.allowed_control_update.remove(updated_object.name)

                #unintentional: restriction will cause co's to have delayed sync
                #need to either update control local
                for updated_object in updated_objects.co:
                    triplet_index = updated_object[TAG_triplet_index]
                    triplet = triplet_buffer[triplet_index]
                    
                    any_axis_restrictive = False
                    for axis in range(0,3):
                        any_axis_restrictive = any_axis_restrictive or (triplet[axis] is None ) or channels[axis].lock
                        
                    if any_axis_restrictive:
                        print_time('restricted: ' + updated_object.name)
                        control_type = 1
                        i = triplet_index
                        ctrl_object = key_objects.grouped[control_type][i]

                        local = Vector((control_locals[0][i][control_type],control_locals[1][i][control_type],control_locals[2][i][control_type]))
                        matrix_index = active_trail_data.get_triplet_frame_index(i,control_type)
                        parent_matrix =  parent_matrix_cache[matrix_index]
                        world = parent_matrix @ local

                        channel_basis = parent_matrix.inverted() @ self.tracking_identity_matrices[matrix_index]
                        _,rot,scale = channel_basis.decompose()
                        channel_basis = matrix_trs(Vector(),rot,scale)#remove location from basis since controls have a defined location
                        world = (parent_matrix @ Matrix.Translation(local) @ channel_basis @ control_offset).decompose()[0]
                        

                        ctrl_object.scale = (1,1,1)
                        ctrl_object.location = world
                        ctrl_object.rotation_quaternion = parent_matrix.to_quaternion()
                        #removing from buffer means, for whatever reason, that the snap will be jittery.  
                        #otherwise, its butter smooth for restricting control to given axis.
                        #self.allowed_control_update.remove(updated_object.name)
                for updated_object in updated_objects.right:
                    triplet_index = updated_object[TAG_triplet_index]
                    triplet = triplet_buffer[triplet_index]
                    
                    any_axis_restrictive = False
                    for axis in range(0,3):
                        any_axis_restrictive = any_axis_restrictive  or (triplet[axis] is None ) or channels[axis].lock or channels[axis].lock or (not is_handle_type_editable(channels[axis].keyframe_points[triplet.indices[axis]].handle_right_type))

                    if any_axis_restrictive:
                        control_type = 2
                        i = triplet_index
                        ctrl_object = key_objects.grouped[control_type][i]

                        local = Vector((control_locals[0][i][control_type],control_locals[1][i][control_type],control_locals[2][i][control_type]))
                        matrix_index = active_trail_data.get_triplet_frame_index(i,control_type)
                        parent_matrix =  parent_matrix_cache[matrix_index]
                        world = parent_matrix @ local

                        channel_basis = parent_matrix.inverted() @ self.tracking_identity_matrices[matrix_index]
                        _,rot,scale = channel_basis.decompose()
                        channel_basis = matrix_trs(Vector(),rot,scale)#remove location from basis since controls have a defined location
                        world = (parent_matrix @ Matrix.Translation(local) @ channel_basis @ control_offset).decompose()[0]
                        

                        ctrl_object.scale = (1,1,1)
                        ctrl_object.location = world
                        ctrl_object.rotation_quaternion = parent_matrix.to_quaternion()
                        #removing from buffer means, for whatever reason, that the snap will be jittery.  
                        #otherwise, its butter smooth for restricting control to given axis.
                        #self.allowed_control_update.remove(updated_object.name)
                            
        else:
            #print_time('write rot' )
            total_channels = active_trail_data.total_channels
            rotation_mode = self.target.rotation_mode
            rot_extract_func = self.rotation_extract_funcs[rotation_mode]

            settings = bpy.context.scene.motion_trail3D_settings
            compatibility_extended = settings.rotation_compatibility == 'EXTENDED'
            compatibility_with_co = settings.rotation_compatibility in {'CO_COMPATIBLE','CO_LEFT_COMPATIBLE','CO_RIGHT_COMPATIBLE','FIRST','LAST'}
            compatibility_with_first = settings.rotation_compatibility == 'FIRST'
            compatibility_with_last = settings.rotation_compatibility == 'LAST'
            compatibility_with_current = settings.rotation_compatibility == 'CURRENT_FRAME'
            rot_mode_quaternion = rotation_mode == 'QUATERNION'
            rot_mode_euler = (not rot_mode_quaternion) and ( rotation_mode != 'AXIS_ANGLE')
            
            #default 0 for compatibility EXTENDED when the offset is used ( compatibility_with_co)
            channel_local_triplet_offset = 0
            if (settings.rotation_compatibility == 'CO_LEFT_COMPATIBLE'):
                channel_local_triplet_offset = -1 
            elif  (settings.rotation_compatibility == 'CO_RIGHT_COMPATIBLE'):
                channel_local_triplet_offset = 1

            #current_frame_triplet_index = 0
            #todo: calc once per triplet buffer recalc (though, at this time 05-18-19, triplet buffer recalc frequently already, I think per write to channels)
            channel_local_current = None
            if compatibility_with_current:
                #current_frame = bpy.context.scene.frame_current
                #xAxis = 0
                #index_co = 1
                ##determine triplet at or before current frame
                #current_frame_triplet_index = 0
                ##[axis][triplet] = (left time, co time, right time)
                #for triplet_index,times in enumerate(active_trail_data.key_times_per_channel[xAxis]):
                #    if times[index_co] <= current_frame:
                #        current_frame_triplet_index = triplet_index
                   

                if rot_mode_quaternion:
                    channel_local_current = Quaternion()
                elif rot_mode_euler:
                    channel_local_current = Euler((0,0,0),rotation_mode)

                current_frame = bpy.context.scene.frame_current
                for channel_index in range(0,total_channels):
                    channel_local_current[channel_index] =  channels[channel_index].evaluate(current_frame)

            #ensuring local's sign matches dot() sign results in negating local if the dot() is negative.
            #also note that we use the channel_local for the control type, not of the associated co.
            #Case where user is attempting to rotate multiple adjacent rot ctrls. 
            #   -latter: adjacent handles (rhandle of left key, lhandle of right key) may flip rotations relative to eachother, discontinuous ipo. Continuous ipo not preserved.
            #   -former: adjacent handles do not flip, continuous ipo preserved.
            #____
            #However, the latter results in more intuitive rotation ipo to and from a co. Former is less intuitive.
            control_type = 0
            channel_local_type = 1 if compatibility_with_co else control_type
            #calculate channel local buffer for rotation compatibility
            #region
            channel_local_buffer = {}
            if compatibility_with_current:
                for updated_object in updated_objects.left:
                    triplet_index = updated_object[TAG_triplet_index]
                    channel_local_buffer[triplet_index] = channel_local_current
            else:
                for updated_object in updated_objects.left:
                    triplet_index = updated_object[TAG_triplet_index]
                    
                    if compatibility_with_co or compatibility_extended:
                        channel_local_triplet_index = clamp(triplet_index + channel_local_triplet_offset,0,len(triplet_buffer)-1)
                    elif compatibility_with_first:
                        channel_local_triplet_index = 0 
                    elif compatibility_with_last:
                        channel_local_triplet_index = -1

                    if rot_mode_quaternion:
                        channel_local = Quaternion()
                        for axis in range(0,total_channels):
                            channel_local[axis] = active_trail_data.key_values_per_channel[axis][channel_local_triplet_index][channel_local_type]
                    elif rot_mode_euler:
                        channel_local = Euler((0,0,0),rotation_mode)
                        for axis in range(0,total_channels):
                            channel_local[axis] = active_trail_data.key_values_per_channel[axis][triplet_index][channel_local_type]
                    
                    channel_local_buffer[triplet_index] = channel_local 
            #endregion
            for updated_object in updated_objects.left:
                triplet_index = updated_object[TAG_triplet_index]
                triplet = triplet_buffer[triplet_index]
                
                matrix_index = active_trail_data.get_triplet_frame_index(triplet_index,control_type)
                parent_matrix = parent_matrix_cache[matrix_index]
                local_matrix = parent_matrix.inverted() @ updated_object.matrix_basis
                #ctrl scale allows user to affect easing 
                #channel_local.scale should be const ref (to co, not to eitehr co or self -> changes scale basis. Ofc, can update all ctrl scales on toggle too)
                #what about co with self? - use relative scale for writes. Relative scale to channel_local.magnitude
                #requires control scale writes to equal cahnel local magnitude....but by that point, we might as well read channel_local magnitude and write directly as scale, then write scale directly for writes.
                #Q: is easing ctrl teh same for euler (I doubt it, scaling probably not even necessary)
                _,_,scale = local_matrix.decompose()
                local = rot_extract_func(local_matrix)

                if rot_mode_quaternion:
                    #without preserving scale, magnitude always 1 (normalized)
                    #_,_,parent_scale = parent_matrix.decompose()
                    #parent_scale = parent_scale[0]
                    local *= math.copysign(1,channel_local_buffer[triplet_index].dot(local)) * scale[0]# * parent_scale 
                elif rot_mode_euler:
                    local.make_compatible(channel_local_buffer[triplet_index])

                for axis in range(0,total_channels):
                    if ((triplet[axis]  is not None )and  not channels[axis].lock) :
                        key = channels[axis].keyframe_points[triplet.indices[axis]]

                        if is_handle_type_editable(key.handle_left_type):
                            key.handle_left = (key.handle_left[0],local[axis])
                            if not active_trail_data.key_objects[2][triplet_index].select_get():
                                align_right_handle(key)
            control_type = 1
            channel_local_type = 1
            #calculate channel local buffer for rotation compatibility
            #region
            channel_local_buffer = {}
            if compatibility_with_current:
                for updated_object in updated_objects.co:
                    triplet_index = updated_object[TAG_triplet_index]
                    channel_local_buffer[triplet_index] = channel_local_current
            else:
                for updated_object in updated_objects.co:
                    triplet_index = updated_object[TAG_triplet_index]
                    
                    if compatibility_with_co or compatibility_extended:
                        channel_local_triplet_index = clamp(triplet_index + channel_local_triplet_offset,0,len(triplet_buffer)-1)
                    elif compatibility_with_first:
                        channel_local_triplet_index = 0 
                    elif compatibility_with_last:
                        channel_local_triplet_index = -1

                    if rot_mode_quaternion:
                        channel_local = Quaternion()
                        for axis in range(0,total_channels):
                            channel_local[axis] = active_trail_data.key_values_per_channel[axis][channel_local_triplet_index][channel_local_type]
                    elif rot_mode_euler:
                        channel_local = Euler((0,0,0),rotation_mode)
                        for axis in range(0,total_channels):
                            channel_local[axis] = active_trail_data.key_values_per_channel[axis][triplet_index][channel_local_type]
                    
                    channel_local_buffer[triplet_index] = channel_local 
            #endregion
            for updated_object in  updated_objects.co:
                #print_time('updated' )
                triplet_index = updated_object[TAG_triplet_index]
                triplet = triplet_buffer[triplet_index]

                matrix_index =active_trail_data.get_triplet_frame_index(triplet_index,control_type)
                parent_matrix =  parent_matrix_cache[matrix_index]
                local_matrix = parent_matrix.inverted() @ updated_object.matrix_basis
                #todo: (???)scaling works breaks if ctrl_type == cahnenl_ctrl type due to compounded scaling
                #ctrl scale allows user to affect easing 
                _,_,scale = local_matrix.decompose()
                local = rot_extract_func(local_matrix)

                if rot_mode_quaternion:
                    #without preserving scale, magnitude always 1 (normalized)
                    #_,_,parent_scale = parent_matrix.decompose()
                    #parent_scale = parent_scale[0]
                    local *= math.copysign(1,channel_local_buffer[triplet_index].dot(local)) * scale[0]# * parent_scale 
                elif rot_mode_euler:
                    local.make_compatible(channel_local_buffer[triplet_index])

                for axis in range(0,total_channels):
                    if ((triplet[axis] is not None) and not channels[axis].lock):
                        key = channels[axis].keyframe_points[triplet.indices[axis]]

                        co_offset = local[axis] - key.co[1]
                        if not active_trail_data.key_objects[0][triplet_index].select_get():
                            offset_left_handle(key,co_offset)
                            
                        if not active_trail_data.key_objects[2][triplet_index].select_get():
                            offset_right_handle(key,co_offset)

                        key.co = (key.co[0], local[axis])

            control_type = 2
            channel_local_type = 1 if compatibility_with_co else control_type
            #calculate channel local buffer for rotation compatibility
            #region
            channel_local_buffer = {}
            if compatibility_with_current:
                for updated_object in updated_objects.right:
                    triplet_index = updated_object[TAG_triplet_index]
                    channel_local_buffer[triplet_index] = channel_local_current
            else:
                for updated_object in updated_objects.right:
                    triplet_index = updated_object[TAG_triplet_index]
                    
                    if compatibility_with_co or compatibility_extended:
                        channel_local_triplet_index = clamp(triplet_index + channel_local_triplet_offset,0,len(triplet_buffer)-1)
                    elif compatibility_with_first:
                        channel_local_triplet_index = 0 
                    elif compatibility_with_last:
                        channel_local_triplet_index = -1

                    if rot_mode_quaternion:
                        channel_local = Quaternion()
                        for axis in range(0,total_channels):
                            channel_local[axis] = active_trail_data.key_values_per_channel[axis][channel_local_triplet_index][channel_local_type]
                    elif rot_mode_euler:
                        channel_local = Euler((0,0,0),rotation_mode)
                        for axis in range(0,total_channels):
                            channel_local[axis] = active_trail_data.key_values_per_channel[axis][triplet_index][channel_local_type]
                    
                    channel_local_buffer[triplet_index] = channel_local 
            #endregion
            for updated_object in  updated_objects.right:
                triplet_index = updated_object[TAG_triplet_index]
                triplet = triplet_buffer[triplet_index]
                
                matrix_index =active_trail_data.get_triplet_frame_index(triplet_index,control_type)
                parent_matrix =  parent_matrix_cache[matrix_index]
                local_matrix = parent_matrix.inverted() @ updated_object.matrix_basis
                #ctrl scale allows user to affect easing 
                _,_,scale = local_matrix.decompose()
                local = rot_extract_func(local_matrix)

                if rot_mode_quaternion:
                    #without preserving scale, magnitude always 1 (normalized)
                    #_,_,parent_scale = parent_matrix.decompose()
                    #parent_scale = parent_scale[0]
                    local *= math.copysign(1,channel_local_buffer[triplet_index].dot(local)) * scale[0]# * parent_scale 
                elif rot_mode_euler:
                    local.make_compatible(channel_local_buffer[triplet_index])

                for axis in range(0,total_channels):
                    if ((triplet[axis]  is not None) and not channels[axis].lock):
                        key = channels[axis].keyframe_points[triplet.indices[axis]]

                        
                        if is_handle_type_editable(key.handle_right_type):
                            key.handle_right = (key.handle_right[0], local[axis])

                            if not active_trail_data.key_objects[0][triplet_index].select_get():
                                align_left_handle(key)
                                
    def calculate_control_worlds(self):
        #print_time('cal ctrl worls')
        #although rot mode ctrls positioned onto trail, results include split keys
        #
        #frame_start,frame_end = self.frame_start,self.frame_end
        
        #[location axis][triplet_index] = (handle left, co, handle right)
        active_trail_data =self.active_trail_data
        control_locals = active_trail_data.key_values_per_channel
        triplet_buffer = active_trail_data.triplet_buffer
        key_objects = active_trail_data.key_objects

        parent_matrix_cache = self.active_parent_matrix_cache  

        control_offset = self.get_control_offset_matrix()
                    
        
        if not self.is_rotation_mode():

            for i in range(0,len(triplet_buffer)):
                #0: handle left, 1:co, 2:handle_right
                for control_type in range(0,3):
                    ctrl_object = key_objects.grouped[control_type][i]

                    if ctrl_object.name not in self.allowed_control_update:
                        local = Vector((control_locals[0][i][control_type],control_locals[1][i][control_type],control_locals[2][i][control_type]))
                        #print_time(f'triplet:{i} control:{("left","co","right")[control_type]} local:{local}')
                        matrix_index = active_trail_data.get_triplet_frame_index(i,control_type)
                        parent_matrix =  parent_matrix_cache[matrix_index]

                        channel_basis = parent_matrix.inverted() @ self.tracking_identity_matrices[matrix_index]
                        _,rot,scale = channel_basis.decompose()
                        channel_basis = matrix_trs(Vector(),rot,scale)#remove location from basis since controls have a defined location
                        world = (parent_matrix @ Matrix.Translation(local) @ channel_basis @ control_offset).decompose()[0]
                        
                        loc_scaling =self.relative_parent_inverse_matrix_cache[matrix_index].inverted().decompose()[2]
                        #for some reason trls are not even being calc wright even without relative parenting . whats oging on?
                        world[0] *= loc_scaling[0] 
                        world[1] *= loc_scaling[1] 
                        world[2] *= loc_scaling[2] 

                        #print_time('scale: ' + str(scale))
                        #maybe i can write to empty's inverse matrix? for a place to write scales without affecting other code?
                        ctrl_object.scale = (1,1,1)
                        ctrl_object.location = world
                        ctrl_object.rotation_quaternion = parent_matrix.to_quaternion()
                        
        else:
            
            rotation_mode = self.target.rotation_mode
            total_channels = active_trail_data.total_channels
            rot_build_func = self.rotation_build_funcs[rotation_mode]
            rotation_extract_funcs = self.rotation_extract_funcs[rotation_mode]

            local = Vector.Fill(total_channels)
            for i in range(0,len(triplet_buffer)):
                #0: handle left, 1:co, 2:handle_right
                for control_type in range(0,3):
                    ctrl_object = key_objects.grouped[control_type][i]

                    if ctrl_object.name not in self.allowed_control_update:
                        
                        for channel_index in range(0,total_channels):
                            local[channel_index] = control_locals[channel_index][i][control_type]

                        matrix_index = active_trail_data.get_triplet_frame_index(i,control_type)
                        parent_matrix =  parent_matrix_cache[matrix_index]
                        world = rotation_extract_funcs((parent_matrix.to_quaternion() @ rot_build_func(local).to_quaternion()).to_matrix().to_4x4())


                        #since rot objs are also time objs, loc set when considered a time obj
                        #ctrl_object.location = self.get_sampled_world_position(matrix_index)
                        self.write_rotation(rotation_mode,ctrl_object,world)
                        
                        
                        ctrl_object.scale = (1,1,1)
                        if rotation_mode == 'QUATERNION':
                            #account for things like armature scaling. In the write to channel func, without this correction, then quat writes will be scaled by 1/armatureSCale (assuming uniform scale)
                            ctrl_object.scale = (local.magnitude,local.magnitude  ,local.magnitude)

                        #required in order for mesh vertex_group rot to be displayed correctly
                        #todo: accoutn for in ctrl write
                        _,_,parent_scale = parent_matrix.decompose()
                        ctrl_object.scale = (ctrl_object.scale[0] * parent_scale[0],ctrl_object.scale[1] * parent_scale[1],ctrl_object.scale[2] * parent_scale[2])

    def get_sampled_world_position(self,frame):
        '''misleading func name: output is relative to current_relative_parent_matrix = root ctrl.matrix_world (with loc scaled)'''
        frame_start,frame_end = self.frame_start,self.frame_end
        #positions = self.trail_location_data.sample_values_per_channel

        matrix_index = clamp(frame,frame_start,frame_end) - frame_start
        parent_matrix = self.tracking_identity_matrices[matrix_index]#self.active_parent_matrix_cache[matrix_index]
        #x = positions[0][matrix_index]
        #y = positions[1][matrix_index]
        #z = positions[2][matrix_index]
        #position_local = Vector((x,y,z))

        trail_offset = self.get_control_offset_vector()

        #return parent_matrix @ position_local 
        return parent_matrix @ trail_offset
   
    def cancel(self,context):
        self.dispose()

    def dispose(self):
        
        

        if self.is_disposed:
            print_time('...already disposed')
            return 

        print_time('diposing motion trail3D ... ')
        
        
        index,item = get_registered_trailOp(self.target_name)
        if item:
            settings = bpy.context.scene.motion_trail3D_settings
            settings.active_trails.remove(index)

        unregister_trailOp(self.target_name)
        self.draw_callback_dns_handle.remove_callback()
        self.scene_update_callback_dns_handle.remove_callback()
        
        
        #print('d')
        settings = bpy.context.scene.motion_trail3D_settings
        
        #print('e')
        if self.is_active_get() or self.ptr_all_control_points_root.exists():
            
            #print('f')
            if self.ptr_all_control_points_root.exists():
                #print('g')
                #true if disposed through pressing ESC
                #False if disposed due to undoing
                objects = bpy.data.objects
                
                #print('h')
                root = self.ptr_all_control_points_root.deref()

                #delete baked world animation created by relative parenting
                if root.animation_data and root.animation_data.action:
                    root.animation_data_clear()

                #print('i')
                for obj in root.children:# in self.object_pool.buffer:
                    #print('j')
                    objects.remove( obj,do_unlink=True)
                #print('k')
                objects.remove(root,do_unlink=True)

            #print('l')
            #collection would be deleted if user did Undo, so only remove if they didnt.
            bpy.data.collections.remove(self.ptr_collection.deref(),do_unlink=True,do_id_user=True,do_ui_user=True)
        
        


        self.reset_instance_fields()
        self.is_disposed = True 
        
        #update outliner view.. (2.79)
        #in 2.80, this causes crash.. and isn't even necessary
        #bpy.context.scene.frame_set(bpy.context.scene.frame_current)
        print_time('.. diposed motion trail3D')
        
        
    def recalculate_triple_buffer(self,settings,force_relink=False,preserve_selection=True):
        #print_time('recalc_triplet_buffer')
        active_trail_data = self.active_trail_data
        updated_objects = active_trail_data.updated_objects
        updated_time_objects = active_trail_data.updated_time_objects
        prev_updated_time_objects = active_trail_data.prev_updated_time_objects

        active_trail_data.generate_triplet_buffer()
        cur_triplet_len = len(active_trail_data.triplet_buffer)

        #print_time('new triplet len: ' + str(cur_triplet_len))
        active_trail_data.moved_time_objects.ensure_size(cur_triplet_len)
        active_trail_data.recalculate_control_values(self.get_target_default_value())
        
        #todo: optimization: consider: based on len difference, just alloc/dealloc from end of ctrl pool?
        expected_in_use_factor = 3 if self.is_rotation_mode() else 6
        #above expected factor only applied when rot controls were also used as their own time ctrls.
        #expected_in_use_factor = 6
        if force_relink or ( cur_triplet_len * expected_in_use_factor != self.object_pool.in_use):#prev_triplet_len != cur_triplet_len:
            #without this flag, new objects willl cause inserted keys to be repositioned at zero.
            self.ignore_control_update_once = True
            self.link_objects_to_triplet_buffer(settings,preserve_selection=preserve_selection)
            
            #print_time('end relinked: ' + str(int(self.object_pool.in_use / expected_in_use_factor)))
            #clear user-hidden controls
            for group in active_trail_data.key_objects:
                for obj in group:
                    obj.hide_set(False)

            for group in active_trail_data.key_time_objects:
                for obj in group:
                    obj.hide_set(False)
        #do func tagging to find where the crash happens
        self.update_control_hide_locked(settings)
        self.calculate_control_worlds()

        #else:
        #    print('no need to add objects' + str(prev_triplet_len))
    def get_target_default_value(self):
        '''[mode-generalized]'''
        default_value = self.target.location 
        if self.is_rotation_mode():
            default_value = self.target_rotations[self.target.rotation_mode]
        return default_value 
    def invoke(self, context, event):
        
        if not context.area.type == 'VIEW_3D':
            self.report({'WARNING'}, "View3D not found, cannot run motion trail3D operator")
            return {'CANCELLED'}

        settings = context.scene.motion_trail3D_settings

        self.reset_instance_fields()
        self.is_disposed=False 
        self.init_motion_trail(context,event)
        trailOp = register_trailOp(self.ptr_active_object.name, self.target_name)
        trailOp.trail_mode = settings.default_trail_mode 
        child_dependency_matrices = self.get_trail_info().child_dependency_matrices
        for _ in range(self.frame_start,self.frame_end+1):
            item = child_dependency_matrices.add()
            item.set_matrix(Matrix.Identity(4))
            
        #if bone connected, then it has no control over its location anyways, so default to rotation mode.
        if self.is_target_bone() and self.target.bone.use_connect:
            trailOp.trail_mode = 'ROTATION'
            #print_time('set to rot')
                
        
        if self.is_target_bone():
            settings = bpy.context.scene.motion_trail3D_settings
            active_trail_targets = {trailOp.target_name for trailOp in settings.active_trails}
            dependency = self.get_trail_info().dependency
            pose_bone = self.target 
            for parent in pose_bone.parent_recursive:
                if parent.name in active_trail_targets:
                    dependency.is_active=True
                    dependency.target_name = parent.name  
                    #use earliest parent
                    break 
                

        self.check_trail_mode_changed()
        active_trail_data = self.active_trail_data
        active_trail_data.generate_triplet_buffer()
        self.init_linking_data()
        active_trail_data.recalculate_control_values(self.get_target_default_value())
        self.link_objects_to_triplet_buffer(settings)

        #calculate the scale to draw control objects based on the user's view
        #only auto calc if this is the first trail to be activated
        if self.is_view_based_scaling() and len(settings.active_trails) == 1:
            region = context.region
            rv3d = context.region_data
            pixel_radius_in_world_start = view3d_utils.region_2d_to_location_3d(region, rv3d, Vector((0,0)),Vector((0,0,1)))
            pixel_radius_in_world_end = view3d_utils.region_2d_to_location_3d(region, rv3d, 6.0 * Vector((1.414,1.414)),Vector((0,0,1)))

            control_base_scale = (pixel_radius_in_world_end - pixel_radius_in_world_start).magnitude

            #zero when 3DView is perpsective instead of orthogonal.
            if(control_base_scale < .001):
                control_base_scale = 1

            control_base_scale *= .5

            if self.is_rotation_mode():
                settings.rotation_controller_scale = control_base_scale * 10.0
            else:
                settings.location_controller_scale = control_base_scale

        '''Non Location Synced Keys buffer'''
        '''
        pre-deref()
        #region
        self.aligned_channels = 0
        if False and settings.sync_nonloc_keys and triplet_len > 0:
            
            #go through all non location channels for active pose bone
            #   check if key in trail range time aligns with a triplet's co time axis
            #       store nonloc key paired with triplet index. Handle offsets calculated at time of drag.
            # workflow: handle times are not time synced. 
            nonloc_channels = [channel for channel in self.action.groups[self.active_pose_bone.name].channels if 'location' not in channel.data_path]
            self.sync_collection = SyncChannelsBuffer(len(nonloc_channels))

            for i,cur_sync_channel in enumerate(nonloc_channels):
                cur_sync_buffer = self.sync_collection.channels[i] = SyncChannelsBuffer.SyncChannel(cur_sync_channel)
            
                triplet_index = 0 
                #triplet.frame accurate only directly after init(). User may drag times afterward and triplet.frame is no longer accurate afterward.
                #triplet.frame not maintained due to not being necessary for any other use.
                loc_frame = round(self.triplet_buffer[triplet_index].frame)
                
                for nonloc_key in cur_sync_channel.keyframe_points:
                    nonloc_frame = round(nonloc_key.co[0])

                    break_loop = False
                    while ( nonloc_frame > loc_frame) and (triplet_index < triplet_len):
                        triplet_index += 1
                        if triplet_index >= triplet_len:
                            break_loop = True
                            break 

                        loc_frame =round(self.triplet_buffer[triplet_index].frame)
                        
                    #todo:limitation: if we link by tirplet index.. thats corrupted after new triplet added or deleted.]
                    if nonloc_frame == loc_frame:
                        cur_sync_buffer.append(nonloc_key,triplet_index,0, 0)
                        
                        triplet_index += 1
                        if triplet_index >= triplet_len:
                            break 

                        loc_frame =round(self.triplet_buffer[triplet_index].frame)

        else:
            #member still created since further useage is only through iteration
            #this prevents need to check for settings.sync_nonloc_keys anymore
            self.sync_collection = SyncChannelsBuffer(0)
            
        #endregion
        '''

        # the arguments we pass the the callback
        #none added due to not being able to make a 1-element tuple..
        #args = (context,None)
        # Add the region OpenGL drawing callback
        # draw in view space with 'POST_VIEW' and 'PRE_VIEW'
        #dont ueven use context as args in case of MEM VIOLATION
        #removed during unregister if script reloaded
        self.draw_callback_dns_handle = DNS_Handle_3DViewDrawHandler(self.target_name,self.draw_callback_px,())
        self.scene_update_callback_dns_handle = DNS_Handle_ScenePostUpdate_Trail(self.target_name,self.scene_update)
        
        self.apply_trail_dependency_flags_change()
        self.apply_trail_dependency_due_parent_xformed()
        self.relative_parent_check_flags_change()
        self.relative_parent_sync_dependency_matrices()
        self.read_sample_points()
        self.calculate_control_worlds()
        self.sync_time_ctrl_locations()

        self.updated_active_object=True
        #wm = bpy.context.window_manager
        #self._timer = wm.event_timer_add(1, context.window)
        context.window_manager.modal_handler_add(self)
        #self.target.location =self.target.location
        #print('invoke done')
        return {'RUNNING_MODAL'}
    
    def init_linking_data(self):
        
        def alloc():
            empty = create_empty(Matrix.Identity(4))
            empty.name = 'trailctrl__' + self.target_name
            self.ptr_collection.deref().objects.link(empty)
            empty.parent = self.ptr_all_control_points_root.deref()
            empty.hide_viewport = True
            empty[TAG_triplet_index]=None
            empty[TAG_control_type]=None
            empty[TAG_value_type]=None
            #empty['in_use']=False 

            #store the object's name instead of a direct reference in case undo occurs.
            #then memory ref is invalidated.
            return IndirectObject(empty.name)

        def realloc(empty):
            #print('reallocating object: ' + empty.name)
            empty.hide_viewport = True
            empty[TAG_triplet_index] = None
            empty[TAG_control_type]=None
            empty[TAG_value_type]=None
            #empty['in_use'] = False 
            empty.parent = self.ptr_all_control_points_root.deref()

            return IndirectObject(empty.name)

        def empty_init(empty):
            empty = empty.deref()
            empty.hide_viewport = False
            empty[TAG_triplet_index] = None
            empty[TAG_control_type]=None
            empty[TAG_value_type]=None
            #empty['in_use'] = True 

        def dealloc(empty):
            empty = empty.deref()
            empty.hide_viewport = True
            empty[TAG_triplet_index] = None
            empty[TAG_control_type]=None
            empty[TAG_value_type]=None
            #empty['in_use'] = False

        self.object_pool = Pool(empty_init,alloc,dealloc,realloc)
        
    def link_objects_to_triplet_buffer(self,settings,preserve_selection=True):
        '''[mode-generalized]'''
        #print_time('begin relink..')
        #generalize: output objs buffer, store in given buffer

        active_trail_data = self.active_trail_data
        triplet_buffer = active_trail_data.triplet_buffer
        key_objects  = active_trail_data.key_objects
        key_time_objects =active_trail_data.key_time_objects

        object_pool = self.object_pool
        base_scale = self.get_controller_scale()
        time_scale = 5.0/4.0
        

        render_trail = self.get_trail_info().render_trail  and  settings.render_trail
        hide_handles = (not settings.show_handles) or (not render_trail)
        hide_co = (not settings.show_co ) or (not render_trail)
        hide_times = (not settings.show_time) or (not render_trail)

        active_sel_triplet = None 
        selection_cache = [[],[],[]]
        #preserve selection only false after undo that results in less existing objects
        #without check, then we may try to deref a lost control
        if preserve_selection and (self.prev_trail_data is not None) and (self.prev_trail_data != self.active_trail_data): 
            #bug: due to unique case of changing to rot mode resulting in more ctrls needed. On undo, objs are lost and prev_trail-data non-None. Thus, there is an attempt
            #to preserve selection on objects that no longer exist...
            #try: don't checkc for changed mode. Just validate, falg to not preserve sel. let next step check for changed mode. Then let step after that handle undo check? (wasted buffer recalc, but not frequently sequence for normal useage)
            #we can use a flag to avoid preserving selection... but it still leads to a deref() missing during a draw call normal deref()...?
            #bugsearch: verify prev_trail_data is actually a different mode (I think I need to clear prev trail data after this?)
            print_undocheck(f'preserving selection from {self.prev_trail_data.mode} to {self.active_trail_data.mode} ')
            #print()
            #print_time()
            #print('caching sel:')
            #active_object = bpy.context.scene.objects.active
            #setting to None results in pivot defaulting to any selection (desired) 
            bpy.context.view_layer.objects.active = None 
            for control_type,objs in enumerate(self.prev_trail_data.key_objects.ptr_grouped):
                current_sel_cache = selection_cache[control_type]
                for triplet_index,ptr_obj in enumerate(objs):
                    #print(obj.name)
                    obj = ptr_obj.deref()
                    current_sel_cache.append(obj.select_get() and is_ctrl_used(obj))

                    #if obj == active_object:
                    #    active_sel_triplet = (control_type,triplet_index,True)
                    #if current_sel_cache[-1] == True:
                    #    print('sel: ' + str(triplet_index) + ' type: ' + str(('Left', 'CO','Right')[control_type]))

            for control_type,objs in enumerate(self.prev_trail_data.key_time_objects.ptr_grouped):
                current_sel_cache = selection_cache[control_type]
                for triplet_index,ptr_obj in enumerate(objs):
                    obj = ptr_obj.deref()
                    current_sel_cache[triplet_index] = current_sel_cache[triplet_index] or (obj.select_get() and is_ctrl_used(obj))
                    
                    #if obj == active_object:
                    #    active_sel_triplet = (control_type,triplet_index,False)
                    #if current_sel_cache[-1] == True:
                    #    print('sel: ' + str(triplet_index) + ' type: ' + str(('Left', 'CO','Right')[control_type]))
            #get rid of old unused references
            self.prev_trail_data.clear_key_objects()
            self.prev_trail_data.clear_updated()
            self.prev_trail_data.prev_updated_time_objects.clear()

        #updates are no longer valid, avoid time and value writes
        active_trail_data.clear_key_objects()
        active_trail_data.clear_updated()
        active_trail_data.prev_updated_time_objects.clear()
        object_pool.dealloc_all()
        
        if not self.is_rotation_mode():
            for triplet_index in  range(0,len(triplet_buffer)):
                ptr_lhandle = object_pool.alloc()
                ptr_co     = object_pool.alloc()
                ptr_rhandle = object_pool.alloc()
                ptr_lhandle_time = object_pool.alloc()
                ptr_co_time = object_pool.alloc()
                ptr_rhandle_time = object_pool.alloc()
                
                lhandle,co,rhandle = ptr_lhandle.deref(),ptr_co.deref(),ptr_rhandle.deref()
                lhandle_time,co_time,rhandle_time = ptr_lhandle_time.deref(),ptr_co_time.deref(),ptr_rhandle_time.deref()
                

                lhandle[TAG_triplet_index]=co[TAG_triplet_index]=rhandle[TAG_triplet_index] = triplet_index
                lhandle[TAG_control_type] = 0
                co[TAG_control_type] = 1
                rhandle[TAG_control_type] = 2
                lhandle_time[TAG_triplet_index]=co_time[TAG_triplet_index]=rhandle_time[TAG_triplet_index] = triplet_index
                lhandle_time[TAG_control_type] = 0
                co_time[TAG_control_type] = 1
                rhandle_time[TAG_control_type] = 2

                lhandle[TAG_value_type] = co[TAG_value_type] = rhandle[TAG_value_type] = 1
                lhandle_time[TAG_value_type] = co_time[TAG_value_type] = rhandle_time[TAG_value_type] = 2

                lhandle.empty_display_type = 'SPHERE'
                co.empty_display_type = 'CUBE'
                rhandle.empty_display_type = 'SPHERE'
                lhandle_time.empty_display_type = 'PLAIN_AXES'
                co_time.empty_display_type = 'ARROWS'
                rhandle_time.empty_display_type = 'PLAIN_AXES'

                lhandle.empty_display_size = base_scale
                co.empty_display_size = base_scale
                rhandle.empty_display_size = base_scale
                lhandle_time.empty_display_size = base_scale*time_scale
                co_time.empty_display_size = base_scale* time_scale
                rhandle_time.empty_display_size = base_scale* time_scale

                lhandle.hide_viewport = hide_handles
                co.hide_viewport = hide_co
                rhandle.hide_viewport = hide_handles
                lhandle_time.hide_viewport = hide_times
                co_time.hide_viewport = hide_times
                rhandle_time.hide_viewport = hide_times
                
                key_objects.ptr_left.append(ptr_lhandle)
                key_objects.ptr_co.append(ptr_co)
                key_objects.ptr_right.append(ptr_rhandle)
                key_time_objects.ptr_left.append(ptr_lhandle_time)
                key_time_objects.ptr_co.append(ptr_co_time)
                key_time_objects.ptr_right.append(ptr_rhandle_time)

                key_objects.left.append(lhandle)
                key_objects.co.append(co)
                key_objects.right.append(rhandle)
                key_time_objects.left.append(lhandle_time)
                key_time_objects.co.append(co_time)
                key_time_objects.right.append(rhandle_time)

                lhandle.scale = co.scale = rhandle.scale = lhandle_time.scale = co_time.scale = rhandle_time.scale = (1,1,1)
        else:
            rotation_mode = self.target.rotation_mode
            
            #for rotation ctrls, time objs are same as rotation value objects
            for triplet_index in  range(0,len(triplet_buffer)):
                #print('triplet index: ' + str(triplet_index))
                ptr_lhandle,ptr_co,ptr_rhandle = object_pool.alloc(),object_pool.alloc(),object_pool.alloc()
                lhandle,co,rhandle = ptr_lhandle.deref(),ptr_co.deref(),ptr_rhandle.deref()
                #match target's rotation mode so the Transformation Orientation gizmos are consistent and allows user to use Gimbal orientation to edit rot curves individually in world space
                lhandle.rotation_mode = co.rotation_mode = rhandle.rotation_mode =  rotation_mode 
                lhandle[TAG_triplet_index]=co[TAG_triplet_index]=rhandle[TAG_triplet_index] = triplet_index
                lhandle[TAG_control_type] = 0
                co[TAG_control_type] = 1
                rhandle[TAG_control_type] = 2
                
                lhandle[TAG_value_type] = co[TAG_value_type] = rhandle[TAG_value_type] = 3

                #lhandle.data = co.data = rhandle.data = self.target.data
                lhandle.empty_display_type = 'ARROWS'
                co.empty_display_type = 'ARROWS'
                rhandle.empty_display_type = 'ARROWS'

                lhandle.empty_display_size = base_scale
                co.empty_display_size = base_scale
                rhandle.empty_display_size = base_scale

                lhandle.hide_viewport = hide_handles
                co.hide_viewport = hide_co
                rhandle.hide_viewport = hide_handles
                
                #ptr_lhandle.rename('(Key:{0}) {1}'.format(triplet_buffer[triplet_index].frame,'Value Left Handle'))
                #ptr_co.rename('(Key:{0}) {1}'.format(triplet_buffer[triplet_index].frame,'Value Co'))
                #ptr_rhandle.rename('(Key:{0}) {1}'.format(triplet_buffer[triplet_index].frame,'Value Right Handle'))

                #lhandle['trail_tag'] ='(Key:{0}) {1}'.format(triplet_buffer[triplet_index].frame,'Value Left Handle')
                #co['trail_tag'] ='(Key:{0}) {1}'.format(triplet_buffer[triplet_index].frame,'Value Co')
                #rhandle['trail_tag'] ='(Key:{0}) {1}'.format(triplet_buffer[triplet_index].frame,'Value Right Handle')

                key_objects.ptr_left.append(ptr_lhandle)
                key_objects.ptr_co.append(ptr_co)
                key_objects.ptr_right.append(ptr_rhandle)
                key_time_objects.ptr_left.append(ptr_lhandle)
                key_time_objects.ptr_co.append(ptr_co)
                key_time_objects.ptr_right.append(ptr_rhandle)

                key_objects.left.append(lhandle)
                key_objects.co.append(co)
                key_objects.right.append(rhandle)
                key_time_objects.left.append(lhandle)
                key_time_objects.co.append(co)
                key_time_objects.right.append(rhandle)
                lhandle.scale = co.scale = rhandle.scale = (1,1,1)
    
        #restore selection
        #print('restoring: ')
        
        #use ptr_group to avoid using stale references
        for control_type,objs in enumerate(key_objects.ptr_grouped):
            current_sel_cache = selection_cache[control_type]
            for triplet_index,ptr_obj in enumerate(objs):
                if triplet_index >= len(current_sel_cache):
                    #print('broke: ' + str(triplet_index))
                    break 
                obj = ptr_obj.deref()
                obj.select_set( current_sel_cache[triplet_index] and is_ctrl_used(obj))
                #if obj.select_get() == True:
                #    print('sel: ' + str(triplet_index) + ' type: ' + str(('Left', 'CO','Right')[control_type]))

        for control_type,objs in enumerate(key_time_objects.ptr_grouped):
            current_sel_cache = selection_cache[control_type]
            for triplet_index,ptr_obj in enumerate(objs):
                if triplet_index >= len(current_sel_cache):
                    #print('broke: ' + str(triplet_index))
                    break 
                obj = ptr_obj.deref()
                obj.select_set( current_sel_cache[triplet_index] and is_ctrl_used(obj))
            #if obj.select_get() == True:
            #    print('sel: ' + str(triplet_index) + ' type: ' + str(('Left', 'CO','Right')[control_type]))
        #if active_sel_triplet:
        #    print('active: ' + str(active_sel_triplet)) 
        #    control_type = active_sel_triplet[0]
        #    triplet_index = active_sel_triplet[1] 
        #    is_value_obj = active_sel_triplet[2]
        #    #if is_value_obj:
        #    #    print('is value')
        #    #    if triplet_index < len(key_objects.grouped[control_type]):
        #    #        bpy.context.scene.objects.active = key_objects.grouped[control_type][triplet_index]
        #    #elif triplet_index < len(key_time_objects.grouped[control_type]):
        #    #        bpy.context.scene.objects.active = key_time_objects.grouped[control_type][triplet_index]
            
    def is_target_bone(self):
        return self.target_type == 'bone'
    def write_rotation(self,rotation_mode,dst_obj,rotation):
        
        if rotation_mode == 'QUATERNION' :
            dst_obj.rotation_quaternion = rotation
        if rotation_mode == 'AXIS_ANGLE' :
            dst_obj.rotation_axis_angle = rotation
        if rotation_mode == 'XYZ'        :
            dst_obj.rotation_euler = rotation
        if rotation_mode == 'XZY'        :
            dst_obj.rotation_euler = rotation
        if rotation_mode == 'YXZ'        :
            dst_obj.rotation_euler = rotation
        if rotation_mode == 'YZX'        :
            dst_obj.rotation_euler = rotation
        if rotation_mode == 'ZXY'        :
            dst_obj.rotation_euler = rotation
        if rotation_mode == 'ZYX'        :
            dst_obj.rotation_euler = rotation
        
    def init_motion_trail(self, context, event):
        
        global crash_stop_everything
        #crash_stop_everything=True

        self.frame_start,self.frame_end = frame_start,frame_end = context.scene.frame_preview_start,context.scene.frame_preview_end
        self.length = length = frame_end-frame_start + 1
        action = context.active_object.animation_data.action
        self.ptr_action = IndirectAction(action.name)
        self.action = action
         
        self.ptr_active_object = IndirectObject(context.active_object.name)
        self.active_object = context.active_object
        self.tracking_identity_matrices = [Matrix.Identity(4)] * length

        self.ptr_channels_location= [
            IndirectChannel(action.name,'location',0),
            IndirectChannel(action.name,'location',1),
            IndirectChannel(action.name,'location',2),
        ]
        self.channels_location = [None,None,None]

        self.ptr_channels_scale = [
            IndirectChannel(action.name,'scale',0),
            IndirectChannel(action.name,'scale',1),
            IndirectChannel(action.name,'scale',2),
        ]
        self.channels_scale = [None,None,None]

        self.ptr_channels_rotation = {
            'QUATERNION' : [
            IndirectChannel(action.name,'rotation_quaternion',0),
            IndirectChannel(action.name,'rotation_quaternion',1),
            IndirectChannel(action.name,'rotation_quaternion',2),
            IndirectChannel(action.name,'rotation_quaternion',3),
            ],
            'AXIS_ANGLE' : [
            IndirectChannel(action.name,'rotation_axis_angle',0),
            IndirectChannel(action.name,'rotation_axis_angle',1),
            IndirectChannel(action.name,'rotation_axis_angle',2),
            IndirectChannel(action.name,'rotation_axis_angle',3),
            ],
            'XYZ'        : [
            IndirectChannel(action.name,'rotation_euler',0),
            IndirectChannel(action.name,'rotation_euler',1),
            IndirectChannel(action.name,'rotation_euler',2),
            ],
            'XZY'        : [
            IndirectChannel(action.name,'rotation_euler',0),
            IndirectChannel(action.name,'rotation_euler',1),
            IndirectChannel(action.name,'rotation_euler',2),
            ],
            'YXZ'        : [
            IndirectChannel(action.name,'rotation_euler',0),
            IndirectChannel(action.name,'rotation_euler',1),
            IndirectChannel(action.name,'rotation_euler',2),
            ],
            'YZX'        : [
            IndirectChannel(action.name,'rotation_euler',0),
            IndirectChannel(action.name,'rotation_euler',1),
            IndirectChannel(action.name,'rotation_euler',2),
            ],
            'ZXY'        : [
            IndirectChannel(action.name,'rotation_euler',0),
            IndirectChannel(action.name,'rotation_euler',1),
            IndirectChannel(action.name,'rotation_euler',2),
            ],
            'ZYX'        : [
            IndirectChannel(action.name,'rotation_euler',0),
            IndirectChannel(action.name,'rotation_euler',1),
            IndirectChannel(action.name,'rotation_euler',2),
            ]
        }        
        self.channels_rotation = {
            'QUATERNION' : [None,None,None,None],
            'AXIS_ANGLE' : [None,None,None,None],
            'XYZ'        : [None,None,None ],
            'XZY'        : [None,None,None ],
            'YXZ'        : [None,None,None ],
            'YZX'        : [None,None,None ],
            'ZXY'        : [None,None,None ],
            'ZYX'        : [None,None,None ],
        }
        self.rotation_build_funcs = {
            'QUATERNION' : (lambda rot : Quaternion(rot).normalized().to_matrix().to_4x4()      ),
            'AXIS_ANGLE' : (lambda rot : Quaternion((rot[1],rot[2],rot[3]),rot[0]).normalized().to_matrix().to_4x4() ),
            'XYZ'        : (lambda rot : Euler(rot,'XYZ').to_matrix().to_4x4()                          ),
            'XZY'        : (lambda rot : Euler(rot,'XZY').to_matrix().to_4x4()                          ),
            'YXZ'        : (lambda rot : Euler(rot,'YXZ').to_matrix().to_4x4()                          ),
            'YZX'        : (lambda rot : Euler(rot,'YZX').to_matrix().to_4x4()                          ),
            'ZXY'        : (lambda rot : Euler(rot,'ZXY').to_matrix().to_4x4()                          ),
            'ZYX'        : (lambda rot : Euler(rot,'ZYX').to_matrix().to_4x4()                          ),
        }
        def axis_angle_extract(matrix):
            result =  matrix.to_quaternion().to_axis_angle()
            return (result[1],result[0][0],result[0][1],result[0][2])

        self.rotation_extract_funcs = {
            'QUATERNION' : (lambda matrix : matrix.to_quaternion()),
            'AXIS_ANGLE' : (lambda matrix : axis_angle_extract(matrix)),
            'XYZ'        : (lambda matrix : matrix.to_euler('XYZ')),
            'XZY'        : (lambda matrix : matrix.to_euler('XZY')),
            'YXZ'        : (lambda matrix : matrix.to_euler('YXZ')),
            'YZX'        : (lambda matrix : matrix.to_euler('YZX')),
            'ZXY'        : (lambda matrix : matrix.to_euler('ZXY')),
            'ZYX'        : (lambda matrix : matrix.to_euler('ZYX')),
        }
        self.rotation_build_funcs['QUATERNION'](Quaternion())
        self.target_rotations = {
            'QUATERNION' : (0,0,0,0),
            'AXIS_ANGLE' : (0,0,0,0),
            'XYZ'        : (0,0,0),
            'XZY'        : (0,0,0),
            'YXZ'        : (0,0,0),
            'YZX'        : (0,0,0),
            'ZXY'        : (0,0,0),
            'ZYX'        : (0,0,0),
        }


        self.trail_location_data = TrailChannelsData('LOCATION', self.ptr_channels_location,self.frame_start,self.frame_end)
        self.trail_rotation_data = {}
        for rot_mode,ptr_channels in self.ptr_channels_rotation.items():
            self.trail_rotation_data[rot_mode] = TrailChannelsData('ROTATION',ptr_channels,self.frame_start,self.frame_end)
        
        if profile:
            wrapped,_ = profile_wrap_functions( self.trail_location_data, {},{})
            self.profiler_items.extend(wrapped)

        #get data path
        #deref()
        #channels
        if context.active_pose_bone is not None:
            bpy.context.scene.tool_settings.lock_object_mode=False
            pose_bone = context.active_pose_bone

            bone_prefix =  'pose.bones["{0}"].'.format(pose_bone.name )
            for channel in self.ptr_channels_location:
                channel.data_path = bone_prefix + channel.data_path
            for channel in self.ptr_channels_scale:
                channel.data_path = bone_prefix + channel.data_path
            for _,channels in self.ptr_channels_rotation.items():
                for channel in channels:
                    channel.data_path = bone_prefix + channel.data_path

            self.target_type = 'bone'
            self.target_name = pose_bone.name 
            #ptr_target.deref().location used to attach bone to trail as it updates. 
            self.ptr_target = IndirectPoseBone(self.ptr_active_object.name,  pose_bone.name)
            self.target = pose_bone

        else:
            self.data_path = 'location'
            self.target_type = 'object'
            self.ptr_target = self.ptr_active_object
            self.target = self.active_object
            self.target_name = context.active_object.name
            
        collection_name = '{0} trail3D'.format(self.target_name)
        
        self.ptr_collection = IndirectCollection(collection_name)
        self.collection = bpy.data.collections.new(collection_name)
        master_collection = bpy.context.view_layer.active_layer_collection.collection
        master_collection.children.link(self.collection )

        #[left handle selectable world position sample], the next two are for co and handle right, then same for next key
        self.perspective_matrix = context.region_data.perspective_matrix.copy()
        #self.perspective = context.region_data.perspective_matrix


        ''' const parent data matrix, self.parent_positions '''
        #region
        #pose_bone.bone.matrix_local is matrix relative to armature in editmode
        #pose_bone.matrix is pose-space final matrix after animation and constraints, in armature (called Pose) space
        self.nonrelative_parent_matrix_cache = [Matrix.Identity(4).copy()] * length
        self.active_parent_matrix_cache = [Matrix.Identity(4).copy()] * length
        self.dependency_matrix_cache = [Matrix.Identity(4).copy()] * length
        self.relative_parent_inverse_matrix_cache = [Matrix.Identity(4).copy()] * length
        #only used to render parent path and line from parent to motion trail bone
        self.parent_positions = [Vector((0,0,0))] * length

        self.calculate_parent_matrix_cache()
        
        #endregion

        self.all_control_points_root = all_control_points_root = create_empty(Matrix.Translation(Vector((0,0,0))),'{0}.motion_trail_root'.format(self.target_name))
        self.ptr_all_control_points_root = IndirectObject(self.all_control_points_root.name)
        self.collection.objects.link(all_control_points_root)
        all_control_points_root.hide_viewport=True
        all_control_points_root.empty_display_size = 0.125/4
        all_control_points_root.empty_display_type = 'PLAIN_AXES'
        #all_control_points_root.rotation_mode='XYZ'

        #print('init done')
    def calculate_parent_matrix_cache(self):
                
        #temporarily disable constraints that result in an inaccurate trail despite appearing to not affect location(or rotation if in rotation mode)
        tmp_deactivated_constraints = [] 
        #these are only the known problematic constraint types 
        problematic_constraints = [bpy.types.DampedTrackConstraint,bpy.types.LockedTrackConstraint,bpy.types.TrackToConstraint,\
                                    bpy.types.StretchToConstraint]
        for con  in self.target.constraints:
            for con_type in problematic_constraints: 
                if isinstance(con,con_type):
                    #write influence to  0 to account for case where mute is animated but influence is not
                    #I'm assuming if one is keyed, the other is not, thereby disabling the con temporarily.
                    tmp_deactivated_constraints.append((con,con.mute,con.influence))
                    con.mute =True 
                    con.influence = 0
            
        scene = bpy.context.scene
        frames_length =  self.frame_end-self.frame_start + 1
        target_is_bone = self.is_target_bone()
        #has_parent = self.target.parent is not None

        cached_frame = scene.frame_current
        frame_start=self.frame_start
        #for i in range(0,frames_length):
        #    self.relative_parent_inverse_matrix_cache[i] = Matrix.Identity(4)
            
        #generalized obtaining identity path (now misnamed: parent matrix cache) to any influence that's independent 
        #of the trail bone (allows for copyloc with offest, childof any parms, transformation xform, etc)
        #todo: above con independence may no longer be true for constraints that are applied after owner (applied as local to owner)
        disable_use_location = False 
        if False and (target_is_bone and (not self.target.bone.use_local_location) and (self.target.parent is not None)):
            disable_use_location=True 
        for i in range(0,frames_length):
            scene.frame_set(i + frame_start)
            
            result_parent_matrix = Matrix.Identity(4)
            #if has_parent:
            if target_is_bone:
                if not disable_use_location:
                    #matrix_channel = matrix_trs(self.target.location,Quaternion(),Vector((1,1,1)))
                    #print_time(f'{i} : {self.target.location}')
                    result_parent_matrix = self.active_object.matrix_world @ self.target.matrix @ self.target.matrix_basis.inverted()

                else:#todo:works for identity matrix and read/write ctrls with only this change. Problem is that tracking points and dep. cache requires target's world space complete xform, but this calc is only correct for location. Trackingpts and dep. cache req rest pose rot and scale too.
                    local_loc,local_rot,local_scale = (self.target.parent.bone.matrix_local.inverted() @ self.target.bone.matrix_local).decompose()
                    
                    #still wrong.
                    _,result_rot,result_scale = (self.active_object.matrix_world @ self.target.matrix @ self.target.matrix_basis.inverted()).decompose()
                    result_loc = (self.active_object.matrix_world @ self.target.parent.matrix @ Matrix.Translation(local_loc)).decompose()[0]
                    #bug: shouldnt include reuslt rot and scale? since that would then make calc ctrl and writes to channels relative to wrong parent matrix.
                    result_parent_matrix = matrix_trs(result_loc,Quaternion(),Vector((1,1,1)))#result_rot,result_scale)

                ##else:#[1/13/20] I don't remember the thing this bottom block was supposed to fix, but it doesn't appear to fix anything. Just breaks the rotation for rot controls. I think it was related to the identity trail? but that seems fine? 
                #    _,arm_from_targetrot,_ = self.target.bone.matrix_local.decompose()
                #    _,arm_from_parentrot,_ = self.target.parent.bone.matrix_local.decompose()
                #    #target's rotation relative to parent in armature space.
                #    rot = (arm_from_parentrot.inverted() @ arm_from_targetrot).to_matrix().to_4x4()
                #    _,parent_pose_rot,_ = self.target.parent.matrix.decompose()
                #    parent_pose_rot = parent_pose_rot.to_matrix().to_4x4()
                #    #note: target.matrix excludes parent hiearchy rotation, 
                #    #we apply the target's relative rotation 
                #    result_parent_matrix = self.active_object.matrix_world @ self.target.matrix @ ( parent_pose_rot @ rot) @ self.target.matrix_basis.inverted()
                
                
            else:
                result_parent_matrix = self.target.matrix_world @ self.target.matrix_basis.inverted()

            self.active_parent_matrix_cache[i] =  result_parent_matrix.copy()
            self.nonrelative_parent_matrix_cache[i] =  result_parent_matrix.copy()
            
        scene.frame_set(cached_frame)

        for i in range(0,frames_length):
            self.parent_positions[i] = self.active_parent_matrix_cache[i].to_translation()
    
        for con,mute,influence in tmp_deactivated_constraints:
            con.mute=mute
            con.influence = influence  

    def get_trail_info(self):
        return get_registered_trailOp(self.target_name)[1]

    def is_active_get(self):
        index,item = get_registered_trailOp(self.target_name)

        if index >= 0:
            return item.is_active
        return False 

    def has_undo_occured(self):
        #check and assignment to nonserialized value in single function since always used this way.
        global nonserialized_undo_tracker
        global_undo_tracker = nonserialized_undo_tracker[self.target_name]
        _,item = get_registered_trailOp(self.target_name) 

        undo_occured = global_undo_tracker != item.undo_tracker

        nonserialized_undo_tracker[self.target_name] =item.undo_tracker

        return undo_occured 
    def increment_undo_tracker(self):
        global nonserialized_undo_tracker

        _,item = get_registered_trailOp(self.target_name) 
        item.undo_tracker += 1
        nonserialized_undo_tracker[self.target_name] += 1
    

    def is_rotation_mode(self):
        return self.get_trail_info().trail_mode =='ROTATION'
        
    def is_view_based_scaling(self):
        settings = bpy.context.scene.motion_trail3D_settings
        return (settings.is_view_based_scaling_rot and self.is_rotation_mode()) or (settings.is_view_based_scaling_loc and not self.is_rotation_mode())
    def get_trail_mode(self):
        return self.get_trail_info().trail_mode 
        
    def get_controller_scale(self):
        settings = bpy.context.scene.motion_trail3D_settings
        return settings.location_controller_scale if not self.is_rotation_mode() else settings.rotation_controller_scale


        
class POSE_PT_Custom_Motion_Trail(bpy.types.Panel):
    bl_idname = "POSE_PT_Custom_Motion_Trail"
    bl_label = "Motion Trail 3D"
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = "Motion Trail 3D"
    
    
    def draw(self,context):
        
        if crash_stop_everything:
            print_time('CSE PT trail')
            return 
        #print_time('POSE_PT_Custom_Motion_Trail...')
        settings = context.scene.motion_trail3D_settings
        
        layout = self.layout.column(align=True)
        
        
        row = layout.row(align=True)
        if len(settings.active_trails) > 0:
            row.operator(POSE_OT_DeactivateAll.bl_idname,text='',icon='CANCEL')
        row.operator(POSE_OT_MotionTrailBeginTag.bl_idname,text='Motion Trail')
        #row.operator(NULL_OT_NULL_OP.bl_idname,text='',icon='BLANK1')
        #row.operator(POSE_OT_AddTrackingPoint.bl_idname,text='',icon='PIVOT_CURSOR')
        #row.prop(settings,'add_tracking_point',text='',icon = 'PIVOT_CURSOR')
        #row.operator(POSE_OT_MeshFromTrackingPoints.bl_idname,text='',icon='OUTLINER_DATA_MESH')
        #row.operator(NULL_OT_NULL_OP.bl_idname,text='',icon='BLANK1')
        row.operator(POSE_OT_PathToMesh.bl_idname,text='',icon='MESH_DATA')
        row.prop(settings,'trail_use_depth',text='',icon='IMAGE_ZDEPTH')
        row.prop(settings,'increased_fcurve_update_while_playing',text='',icon='NEXT_KEYFRAME')
        row.prop(settings,'increased_ctrl_update_while_playing',text='',icon='FRAME_NEXT')
        #row.operator(NULL_OT_NULL_OP.bl_idname,text='',icon='BLANK1')
        row.prop(settings,'foldout',text='',icon='DOWNARROW_HLT' if settings.foldout else  'RIGHTARROW')
        if settings.foldout:
            
            if settings.default_trail_mode =='ROTATION':
                #box = layout.box()
                col = layout.column(align=True)
                col.prop(settings,'default_trail_mode',text='')
                if settings.default_trail_mode == 'ROTATION':
                    col.prop(settings,'rotation_compatibility',text='')
                    #col.operator(POSE_OT_Flip_Quaternion_Ipo_Direction.bl_idname)
            else:
                col = layout.column(align=True)
                col.prop(settings,'default_trail_mode',text='')
                

            #box = layout.box()
            col = layout.column(align=True)
            
            
            col.prop(settings,'render_trail',text='Render Trail',icon='HIDE_OFF' if settings.render_trail else 'HIDE_ON')

            row = col.row(align=True)
            row.prop(settings,'show_co',text='Co',icon = 'HIDE_OFF' if settings.show_co else 'HIDE_ON')
            row.operator(POSE_OT_show_hidden_co.bl_idname,text='',icon='VIS_SEL_11',emboss=True)
            
            row = col.row(align=True)
            row.prop(settings,'show_handles',text='Handles',icon = 'HIDE_OFF' if settings.show_handles else 'HIDE_ON')
            row.operator(POSE_OT_show_hidden_handles.bl_idname,text='',icon='VIS_SEL_11',emboss=True)
            
            row = col.row(align=True)
            #if settings.default_trail_mode == 'LOCATION':
            row.prop(settings,'show_time',text='Time Handles',icon = 'HIDE_OFF' if settings.show_time else 'HIDE_ON')
            row.operator(POSE_OT_show_hidden_time.bl_idname,text='',icon='VIS_SEL_11',emboss=True)
            #else:
            #    col.label(text='Time Handles',icon = 'HIDE_OFF' )
            col.prop(settings,'show_identity_trail',text='Identity Trail',icon = 'HIDE_OFF' if settings.show_identity_trail else 'HIDE_ON')

            #layout.separator()
            
            #box = layout.box()
            #col = box.column(align=True)
            #col.prop(settings,'sync_nonloc_keys',text='Time-Sync Non-Location Keys')
            
            col=layout.column(align=True)
            col.prop(settings,'selection_sync_type',text='')
            #layout.separator()

            #limit_control_visibility = settings.limit_control_visibility
            #box = layout.box()
            #if limit_control_visibility.active:
            #    col = box.column(align=True)
            #    col.prop(limit_control_visibility,'active',text='Limit Control Visibility')
            #    if limit_control_visibility.active:
            #        col.prop(limit_control_visibility,'handles_use_co_time',text='Show Handles With Co')
            #        col.prop(limit_control_visibility,'range')
            #else:
            #    col = box.column(align=True)
            #    col.prop(limit_control_visibility,'active',text='Limit Control Visibility')
            #layout.separator()

            #since mul trails may be showing with different modes, just show both scales
            row = layout.row(align=True)
            row.prop(settings,'is_view_based_scaling_loc',text='')
            row.prop(settings,'location_controller_scale')
            row = layout.row(align=True)
            row.prop(settings,'is_view_based_scaling_rot',text='' )
            row.prop(settings,'rotation_controller_scale')

            col = layout.column(align=True)
            row = col.row(align=True)
            row.prop(settings,'enable_relative_parent',text='')
            row.label(text='Trail Relative Parent')

            col = layout.column(align=True)
            row = col.row(align=True)
            row.label(text='',icon='BLANK1')
            if settings.enable_relative_parent or len(settings.relative_parent_object) > 0:
                row.prop_search(settings,'relative_parent_object',bpy.data,'objects',text='Parent',icon = 'ERROR' if settings.relative_parent_object not in bpy.data.objects else 'CHECKMARK')
            else:
                row.prop_search(settings,'relative_parent_object',bpy.data,'objects',text='Parent')
            

            col = layout.column(align=True)
            row = col.row(align=True)
            if settings.relative_parent_object in bpy.data.objects:
                parent_data = bpy.data.objects[settings.relative_parent_object].data 
                if isinstance(parent_data,bpy.types.Armature):
                    row.label(text='',icon='BLANK1')
                    row.prop_search(settings,'relative_parent_bone',parent_data,'bones',text='Bone',icon = 'ERROR' if settings.relative_parent_bone not in parent_data.bones else 'CHECKMARK')
                #not alllowed to change settings in UI draw funcs..
                #elif settings.relative_parent_bone != "":
                #    settings.relative_parent_bone = "" 
               
            row = layout.row(align=True)
            row.label(text='',icon='BLANK1')
            row.prop(settings,'relative_parent_render_world',text='Show World Trail')
            
        #print_time('...POSE_PT_Custom_Motion_Trail')
        
class POSE_PT_Custom_Motion_Trail_Active_Trails(bpy.types.Panel):
    bl_label ='Active Trails'
    bl_parent_id ='POSE_PT_Custom_Motion_Trail'
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = "Motion Trail 3D"
    
    def draw(self,context):
        
        if crash_stop_everything:
            print_time('CSE PT active trails')
            return 
        
        layout = self.layout.column(align=True)
        settings = context.scene.motion_trail3D_settings
        
        valid_dependency_targets = {trail.target_name for trail in settings.active_trails}
        for trailOp in settings.active_trails:
            row = layout.row(align=True)
            op = row.operator(POSE_OT_Deactivate.bl_idname,text='',icon='CANCEL')
            op.target_name = trailOp.target_name

            expanded = trailOp.expanded

            if not expanded:
                #row.prop(trailOp,'target_name',text='')
                row.prop(trailOp,'target_name',text='')
                row.prop(trailOp,'render_trail',text='',icon='HIDE_OFF')
                


                row.prop(trailOp,'refresh',text='',icon='FILE_REFRESH')
                row.prop(trailOp,'expanded',text='',icon='DISCLOSURE_TRI_RIGHT')
            else:
                #row.prop(trailOp,'render_trail',text=trailOp.target_name,icon='HIDE_OFF')
                row.prop(trailOp,'target_name',text='')
                row.prop(trailOp,'render_trail',text='',icon='HIDE_OFF')
                row.prop(trailOp,'refresh',text='',icon='FILE_REFRESH')
                row.prop(trailOp,'expanded',text='',icon='DISCLOSURE_TRI_DOWN')
                row = layout.row(align=True)
                row.prop(trailOp,'trail_mode',text='')
                
                if trailOp.object_name  == trailOp.target_name:#then object
                    layout.prop_search(trailOp,'control_offset_tracker_name',bpy.data.objects[trailOp.object_name].motion_trail3D,'tracking_points', text='Offset to')
                else:
                    layout.prop_search(trailOp,'control_offset_tracker_name',bpy.data.objects[trailOp.object_name].pose.bones[trailOp.target_name].motion_trail3D,'tracking_points', text='Offset to')
                    

                row = layout.row(align=True)
                dependency = trailOp.dependency
                
                #row.label(text='Dependency')
                row.prop(dependency,'is_active',text='Dependency')
                row = layout.row(align=True)
                if  len(dependency.target_name) > 0:
                    #row.prop(dependency,'target_name',text='',icon='ERROR' if( dependency.target_name not in valid_dependency_targets ) else 'CHECKMARK' )
                    row.prop_search(dependency,'target_name',settings,'active_trails', text='',icon='ERROR' if( dependency.target_name not in valid_dependency_targets ) else 'CHECKMARK' )
                else:
                    row.prop_search(dependency,'target_name',settings,'active_trails',text='',icon='BLANK1')
                    
                
                #if dependency.foldout:#target_name in valid_dependency_targets:
                col = layout.column(align=True)
                row = col.row(align=True)
                row.label(text='Loc',icon='BLANK1')
                #row.label(text='',icon='BLANK1')
                row.prop(dependency,'inherit_loc',text='')
                row = col.row(align=True)
                row.label(text='Rot',icon='BLANK1')
                row.prop(dependency,'inherit_rot',text='')
                #row.operator(NULL_OT_NULL_OP.bl_idname,text='')
                row = col.row(align=True)
                row.label(text='Scale',icon='BLANK1')
                row.prop(dependency,'inherit_scale',text='')
                #row.operator(NULL_OT_NULL_OP.bl_idname,text='')
                #row = layout.row(align=True)
                #row.label(text='',icon='BLANK1')
                #row.prop(dependency,'keep_self_rot')
            layout.separator()
            

def draw_tracker_panel(layout,settings,tracking_infos,is_bone):
    
        #layout.label(text='Defaults')
        row = layout.row(align=True)
        op = row.operator(POSE_OT_ClearTrackingPoints.bl_idname,text='',icon='CANCEL')
        op.is_bone=is_bone
        row.operator(NULL_OT_NULL_OP.bl_idname,text='')
        row.prop(settings,'show_tracking',text='',icon = 'HIDE_OFF' if settings.show_tracking else 'HIDE_ON')
        #row.label(text='',icon='SCULPT_DYNTOPO')
        #row.label(text='',icon='SCULPT_DYNTOPO')
        #row.operator(POSE_OT_AddTrackingPoint.bl_idname,text='',icon='PIVOT_CURSOR')
        op = row.operator(POSE_OT_AddTrackingPoint.bl_idname,text='',icon='PIVOT_CURSOR')
        op.is_bone=is_bone
        op = row.operator(POSE_OT_MeshFromTrackingPoints.bl_idname,text='',icon='OUTLINER_DATA_MESH')
        op.is_bone=is_bone
        op = row.operator(POSE_OT_CreateAxesTrackingPoints.bl_idname,text='',icon='OUTLINER_DATA_EMPTY')
        op.is_bone=is_bone
        row.prop(settings,'tracker_use_depth',text='',icon='IMAGE_ZDEPTH')

        #box = layout.box()
        separate_next= True 
        for index,tracking_info in enumerate(tracking_infos):
            if separate_next:
                layout.separator()
            separate_next = False 

            col = layout.column(align=True)
            row = col.row(align=True)
            op = row.operator(POSE_OT_ClearTrackingPoint.bl_idname,text='',icon='CANCEL')
            op.index=index
            op.is_bone=is_bone
            #row.operator(NULL_OT_NULL_OP.bl_idname,text='')
            row.prop(tracking_info,'name',text='')
            row.prop(tracking_info,'show_tracking',text='',icon = 'HIDE_OFF' if tracking_info.show_tracking else 'HIDE_ON')
            row.prop(tracking_info,'show_continuous',text='',icon = 'OUTLINER_DATA_CURVE')
            row.prop(tracking_info,'show_lines_from_target',text='',icon = 'ITALIC')
            op = row.operator(POSE_OT_ResetTrackingPoint.bl_idname,text='',icon='PIVOT_CURSOR')
            op.index=index
            op.is_bone=is_bone
            
            op = row.operator(POSE_OT_MeshFromTrackingPoint.bl_idname,text='',icon='OUTLINER_DATA_MESH')
            op.index=index
            op.is_bone=is_bone
            
            row.prop(tracking_info,'foldout',text='',icon='DOWNARROW_HLT' if settings.foldout else  'RIGHTARROW')
            if tracking_info.foldout:
                separate_next=True 
                row = col.row(align=True)
                #row = col.row(align=True)
                col.prop(tracking_info,'location_x',text='x')
                col.prop(tracking_info,'location_y',text='y')
                col.prop(tracking_info,'location_z',text='z')
                col.prop(tracking_info,'length',text='len')

                row = col.row(align=True)
                row.prop(tracking_info,'color_tracking_active',text='')
                row = col.row(align=True)
                row.prop(tracking_info,'ptcolor_tracking_prior',text='')
                row.prop(tracking_info,'ptcolor_tracking_post',text='')
                row.prop(tracking_info,'ptsize_tracking',text='')
                row = col.row(align=True)
                row.prop(tracking_info,'lcolor_tracking_prior',text='')
                row.prop(tracking_info,'lcolor_tracking_post',text='')
                row.prop(tracking_info,'lsize_tracking',text='')
class OBJECT_PT_Tracker_Points(bpy.types.Panel):
    bl_idname = "OBJECT_PT_tracker_points_object"
    bl_label = "Motion Trail Tracking Points"
    bl_space_type = 'PROPERTIES'
    bl_region_type = 'WINDOW'
    bl_context = "object"
            
    @classmethod
    def poll(cls,context):
        return context.active_object
        
    def draw(self,context):
        
        if crash_stop_everything:
            print_time('CSE PT tracker points')
            return 
        layout = self.layout.column(align=True)
        settings = context.scene.motion_trail3D_settings
        
        tracking_infos = context.active_object.motion_trail3D.tracking_points

        draw_tracker_panel(layout,settings,tracking_infos,False)

class BONE_PT_Tracker_Points(bpy.types.Panel):
    bl_idname = "POSE_PT_tracker_points_bone"
    bl_label = "Motion Trail Tracking Points"
    bl_space_type = 'PROPERTIES'
    bl_region_type = 'WINDOW'
    bl_context = "bone"
            
    @classmethod
    def poll(cls,context):
        return  context.active_pose_bone and context.mode == 'POSE'

    def draw(self,context):
        
        if crash_stop_everything:
            print_time('CSE root trail ordered callback')
            return 
        
        layout = self.layout.column(align=True)
        settings = context.scene.motion_trail3D_settings
        
        tracking_infos = context.active_pose_bone.motion_trail3D.tracking_points
        draw_tracker_panel(layout,settings,tracking_infos,True)
class TrackingPoint(PropertyGroup):
    foldout : BoolProperty(default=True)
    name : StringProperty()
    show_tracking : BoolProperty(name='Show TrackingPt Trails',default=True)
    show_continuous : BoolProperty(name='Draw Continuous',default=True )
    show_lines_from_target : BoolProperty(name='Draw From Target',default = False)

    ptsize_tracking : IntProperty(name='Point Size',default = 3,subtype='PIXEL')
    
    ptcolor_tracking_prior : FloatVectorProperty(name='Line Color',soft_min=0,soft_max=1, subtype='COLOR',default = (0.000000, 0.459871, 0.289773))
    ptcolor_tracking_post : FloatVectorProperty(name='Line Color', soft_min=0,soft_max=1,subtype='COLOR',default = (0.000000, 0.459871, 0.289773))
    lcolor_tracking_prior : FloatVectorProperty(name='Line Color', soft_min=0,soft_max=1,subtype='COLOR',default =(0.000000, 0.459871, 0.289773))
    lcolor_tracking_post : FloatVectorProperty(name='Line Color', soft_min=0,soft_max=1,subtype='COLOR',default =(0.000000, 0.459871, 0.289773))
    lsize_tracking : IntProperty(name='Line Thickness',default = 1,subtype='PIXEL')
    color_tracking_active : FloatVectorProperty(name='Color Active', soft_min=0,soft_max=1,subtype='COLOR',default = (0,float( 0.800000 * 1.0),float( 0.500000 * 1.0)))
    location_x : FloatProperty(name='relative X',default=0)
    location_y : FloatProperty(name='relative Y',default=0)
    location_z : FloatProperty(name='relative Z',default=0)

    def get_length(self):
        return self.get_location().magnitude 
    def set_length(self,value):

        location = self.get_location().normalized() * abs(value) 
        self.set_location(location)
        #not sure why changes to length doesn't update in the view? location changes show up in the view...
        bpy.context.scene.frame_set(bpy.context.scene.frame_current)#redraw..
       
    #helper for tracking pts that represent axes
    length : FloatProperty(min=0,set=set_length,get=get_length)

    def set_location(self,location):
        self.location_x,self.location_y,self.location_z = location
    def get_location(self):
        return Vector((self.location_x,self.location_y,self.location_z)) 
    
    
class Vector4Property(bpy.types.PropertyGroup):
    v0 : FloatProperty()
    v1 : FloatProperty()
    v2 : FloatProperty()
    v3 : FloatProperty()

    def set_vector4(self,vec):
        #read from indices in case caller sends a tuple instead of a Vector
        self.v0,self.v1,self.v2,self.v3 = vec[0],vec[1],vec[2],vec[3]

    def set_floats(self,f0,f1,f2,f3):
        self.v0,self.v1,self.v2,self.v3 = f0,f1,f2,f3
    def get(self):
        return Vector((self.v0,self.v1,self.v2,self.v3))
class Matrix4x4Property(PropertyGroup):
    row0 : PointerProperty(type=Vector4Property)
    row1 : PointerProperty(type=Vector4Property)
    row2 : PointerProperty(type=Vector4Property)
    row3 : PointerProperty(type=Vector4Property)

    def set_matrix(self,matrix):
        self.row0.set_vector4(matrix[0])
        self.row1.set_vector4(matrix[1])
        self.row2.set_vector4(matrix[2])
        self.row3.set_vector4(matrix[3])

    def set_vector4(self,r0,r1,r2,r3):
        self.row0.set_floats(r0)
        self.row1.set_floats(r1)
        self.row2.set_floats(r2)
        self.row3.set_floats(r3)

    def get(self):
        return Matrix((self.row0.get(),self.row1.get(),self.row2.get(),self.row3.get()))
class StringPropertyWrapper(PropertyGroup):
    text : StringProperty()
    cache_description : StringProperty()
class DependencyInfo(PropertyGroup):
    foldout :BoolProperty(default=False)
    is_active : BoolProperty('Is Active')
    #to support allowing multiple trails to be editted that include a dependency on eachother                
    target_name : StringProperty('Trail Dependency')
    
    inherit_loc : EnumProperty(name='Loc',
                                description="Parts of dependency trail that affects this trail's location",
                                default='FULL',
                                items=[('FULL','Full','Location Rotation and Scale used.'),
                                        ('LOC',"Loc",''),
                                        ('LOCROT',"LocRot",''),
                                        ('LOCSCALE',"LocScale",''),
                                        ('NONE',"Ignore",''),
                                        ])
                                        
    inherit_rot : BoolProperty(name='Rot',default=True)
    inherit_scale : BoolProperty(name='Scale',default=True)

    def is_inherit_FULL(self):
        return self.inherit_loc == 'FULL' and self.inherit_rot and self.inherit_scale
    
class TrailOp(PropertyGroup):
    
    def get_name(self):
        return self.name 
    def set_name(self,value):
        self.name = value 

    expanded : BoolProperty(name='Expanded')
    name : StringProperty()#todo: repalce for target_name, this field added so trail op can be used as selection item for dep. trails
    object_name : StringProperty()
    target_name : StringProperty('Target',description='WARNING: Do not change this value. It\'s only editable to allow quick copy+pasting as a dependency trail name',get=get_name,set=set_name)
    is_active : BoolProperty('Is Active')
    refresh : BoolProperty('Refresh',default=False)    
    undo_tracker : IntProperty(default=0)
    render_trail : BoolProperty(name='Render',default=True)

    
    trail_mode : EnumProperty(items=[('LOCATION','Location','trail controls allow editting target\'s location channels in world space'),
                                        ('ROTATION','Rotation','trail controls allow editting target\'s rotation channels in world space')],
                                        name='Channel Mode',
                                        description='Trail Mode',
                                        default='LOCATION')

    dependency : PointerProperty(type=DependencyInfo)
    #used by other trails who depend on this trail.
    child_dependency_matrices : CollectionProperty(type=Matrix4x4Property)
    #used by other trails, to avoid updating on same step as this trail. This is so xforms happen in order of parent to children resulting in correct local values being written
    has_updated : BoolProperty(default=False)
    hierarchy_has_updated : BoolProperty(default=False)


    control_offset_tracker_name : StringProperty()



class MotionTrail3DSettings(PropertyGroup):
    foldout : BoolProperty(name='',default=True)

    is_active : BoolProperty(name='Is Active',default=False)
    active_trails : CollectionProperty(type=TrailOp)
    improved_efficiency : BoolProperty(name='Improved Efficiency',default=False)
    render_trail : BoolProperty(name='Render',default=True)

    default_trail_mode : EnumProperty(items=[('LOCATION','Location','trail controls allow editting target\'s location channels in world space'),
                                        ('ROTATION','Rotation','trail controls allow editting target\'s rotation channels in world space')],
                                        name='Channel Mode',
                                        description='Trail Mode ',
                                        default='LOCATION')
    #left/right useful to continue rotations 
    rotation_compatibility : EnumProperty(items=[('CO_COMPATIBLE','Co Compatible','L/R Handle rotation writes limited to 180 degrees from the parent co control'),
                                        ('CO_LEFT_COMPATIBLE','Left Co Compatible','rotation writes limited to 180 degrees from the adjacent left co control'),
                                        ('CO_RIGHT_COMPATIBLE','Right Co Compatible','rotation writes limited to 180 degrees from the adjacent right co control'),
                                        ('EXTENDED','Extended','rotation writes not range limited'),
                                        ('CURRENT_FRAME','Timeline Frame','rotation writes limited to 180 degrees from the rotation channels sampled at the current timeline frame'),
                                        ('FIRST','First',' rotation writes limited to 180 degrees from the first co control'),
                                        ('LAST','Last','rotation writes limited to 180 degrees from the last co control')],
                                        name='Rotation Compatibility',
                                        description='For rotation writes for controls, whether to keep the result within 180 degrees from their related co control',
                                        default='CO_COMPATIBLE')
    sync_nonloc_keys : BoolProperty(name='Time-Sync Non Translation Keys',default=False,description='Time sync rotation keys to translation keys')
    is_view_based_scaling_loc : BoolProperty(name='View-Dependent Location Control Scale',description='On trail start, automatically calculate control scales',default=True)
    is_view_based_scaling_rot : BoolProperty(name='View-Dependent Rotation Control Scale ',description='On trail start, automatically calculate control scales',default=True)

    trail_use_depth : BoolProperty(name='Trail Use Depth Buffer',default=False)
    #limit_control_visibility : PointerProperty(type=ControlVisiblity)

    location_controller_scale : FloatProperty(name='Loc Ctrl Scale', default = 1,precision=4,step=1,soft_min=.000001,min=.000001)
    rotation_controller_scale : FloatProperty(name='Rot Ctrl Scale', default = 1,precision=4,step=1,soft_min=.000001,min=.000001)
    #(default) changes from Fcurve are synced to value objects
    #otherwise (below true) then time objects are selection synced from fcurve changes. 
    selection_sync_type : EnumProperty(items=[('VALUE','Sel. Sync Value','trail co/handle control objects selection synced after changes to fcurve'),
                                        ('TIME','Sel. Sync Time','trail time control objects selection synced after changes to fcurve'),
                                        ('NONE','Sel. Sync None','do not select any control objects after changes to fcurve')],
                                        name='Selection Sync',
                                        description='selection sync FCurve keys to trail control objects',
                                        default='NONE')


    enable_relative_parent : BoolProperty(name='Enable Relative Parent',default=False)
    relative_parent_render_world : BoolProperty(name='Show World Trail',default=True)
    relative_parent_object : StringProperty(name='Relative Parent')
    relative_parent_bone : StringProperty(name='Relative Parent Bone')

    show_co : BoolProperty(name='Show Handles',default=True)
    show_handles : BoolProperty(name='Show Handles',default=True)
    show_time : BoolProperty(name='Show Times',default=False)
    show_identity_trail : BoolProperty(name='Show Identity Trail',default=False)
    show_tracking : BoolProperty(name='Show TrackingPt Trails',default=True)
    show_hidden_co : BoolProperty(name='Show Hidden Co',default=False)
    show_hidden_handles : BoolProperty(name='Show Hidden Handles',default=False)
    show_hidden_time : BoolProperty(name='Show Hidden Times',default=False)

    tracker_use_depth : BoolProperty(name='Tracker Use Depth Buffer',default=False)
    increased_fcurve_update_while_playing : BoolProperty(name='Increased Control Update Rate While Animation Playing',default=True,description='Allows real time editing while animation playing. Whether to try to attempt to force scene to update while animation playing to try and increase trail update rate. Note: Only works as long as scene hitting render target FPS. Disabling will increase playback FPS.')
    increased_ctrl_update_while_playing : BoolProperty(name='Increased FCurve Update Rate While Animation Playing',default=True,description='Allows real time Graph Editor editting while animation playing, independent of whether or not target FPS hit. Whether to resample local channels while animation playing. ')

class MotionTrail3DPropertyObject(PropertyGroup):
    tracking_points : CollectionProperty(type=TrackingPoint)
    #rotation_display_mode : PointerProperty(type= DisplayMeshInfoObject)

class MotionTrail3DPropertyBone(PropertyGroup):
    tracking_points : CollectionProperty(type=TrackingPoint)
    #rotation_display_mode : PointerProperty(type= DisplayMeshInfoBone)

class MotionTrailPreferences(AddonPreferences):
    # this must match the add-on name, use '__package__'
    # when defining this in a submodule of a python package.
    bl_idname = __name__

    ptcolor_prior_frames : FloatVectorProperty(name='Point Pre Frame Color', soft_min=0,soft_max=1,subtype='COLOR',default =(1,1,1))
    ptcolor_post_frames : FloatVectorProperty(name='Point Post Frame Color',soft_min=0,soft_max=1, subtype='COLOR',default =(1,1,1))
    ptsize_sample : IntProperty(name='Point Size',default = 3,subtype='PIXEL')

    lcolor_prior_frames : FloatVectorProperty(name='Line Frame Color', soft_min=0,soft_max=1,subtype='COLOR',default =(.8,.8,.8))
    lcolor_post_frames : FloatVectorProperty(name='Line Frame Color', soft_min=0,soft_max=1,subtype='COLOR',default =(0,0,0))
    lsize_sample : IntProperty(name='Line Size',default = 1,subtype='PIXEL')

    color_handle : FloatVectorProperty(name='Color', soft_min=0,soft_max=1,subtype='COLOR',default =(0.0, 0.5, 0.0))
    lsize_handle : IntProperty(name='Line Size',default = 4,subtype='PIXEL')

    ptcolor_handle_timeA : FloatVectorProperty(name='Point Color', soft_min=0,soft_max=1,subtype='COLOR',default = (0.154203, 0.241336, 0.600000))
    ptcolor_handle_timeB : FloatVectorProperty(name='Point Color Alt', soft_min=0,soft_max=1,subtype='COLOR',default = (0.600000, 0.036825, 0.085719))
    ptsize_time : IntProperty(name='Point Size',default = 7 ,subtype='PIXEL')
    lcolor_handle_timeA : FloatVectorProperty(name='Line Color',soft_min=0,soft_max=1, subtype='COLOR',default = (.8/2,.8/2,2/2))
    lcolor_handle_timeB : FloatVectorProperty(name='Line Color Alt', soft_min=0,soft_max=1,subtype='COLOR',default = (2/2,.8/2,.8/2))
    lsize_time : IntProperty(name='Line Size',default = 4,subtype='PIXEL' )
    
    color_identity_path : FloatVectorProperty(name='Path Color', soft_min=0,soft_max=1,subtype='COLOR',default = (0,.5,.5))
    lsize_identity_path : IntProperty(name='Path Thickness',default = 1,subtype='PIXEL')
    color_identity_line : FloatVectorProperty(name='Line Color', soft_min=0,soft_max=1,subtype='COLOR',default = (0,.8,.5))

    ptsize_tracking : IntProperty(name='Point Size',default = 3,subtype='PIXEL')
    ptcolor_tracking_prior : FloatVectorProperty(name='Line Color',soft_min=0,soft_max=1, subtype='COLOR',default =  (0.916345, 0.936860, 1.000000))
    ptcolor_tracking_post : FloatVectorProperty(name='Line Color',soft_min=0,soft_max=1, subtype='COLOR',default =  (0.916345, 0.936860, 1.000000))
    lcolor_tracking_prior : FloatVectorProperty(name='Line Color',soft_min=0,soft_max=1, subtype='COLOR',default = (0.000000, 1.097335, 0.683171))
    lcolor_tracking_post : FloatVectorProperty(name='Line Color', soft_min=0,soft_max=1,subtype='COLOR',default = (0.013267, 0.565723, 0.676810))
    lsize_tracking : IntProperty(name='Line Thickness',default = 1,subtype='PIXEL')
    color_tracking_active : FloatVectorProperty(name='Color Active',soft_min=0,soft_max=1, subtype='COLOR',default = (0.000000, 1.097335, 0.683171))
    lsize_tracking_active : IntProperty(name='Line Size Active',default = 3,subtype='PIXEL')
    
    #won't work if disabled since draw() won't call scene update().
    #auto_delete_ctrl_animation :BoolProperty(name='Auto Delete 3D Control Animation',default=True,description='!Experimental! Animating 3D trail controls is undefined behaviour. Leave this off.')

    def draw(self, context):
        layout = self.layout
        layout.label(text="Trail Drawing Preferences")

        #row = layout.row(align=True)
        #row.label(text='!Experimental!',icon='ERROR')
        #row.prop(self,'auto_delete_ctrl_animation')
        col = layout.column(align=True)
        col.label(text='Co (Prior - Post Frame)')
        row = col.row(align=True)
        #row.label(text='Points')
        row.prop(self,'ptcolor_prior_frames',text='')
        row.prop(self,'ptcolor_post_frames',text='')
        row.prop(self,'ptsize_sample',text='Point Size')
        row = col.row(align=True)
        #row.label(text='Lines')
        row.prop(self,'lcolor_prior_frames',text='')
        row.prop(self,'lcolor_post_frames',text='')
        row.prop(self,'lsize_sample',text='Line Size')

        #box = layout.box()
        col = layout.column(align=True)
        col.label(text='Handles')
        row = col.row(align=True)
        row.prop(self,'color_handle',text='')
        row.prop(self,'lsize_handle',text='')

        #box = layout.box()
        col = layout.column(align=True)
        col.label(text='Time Handles (Left - Right Handle)' )
        row = col.row(align=True)
        #8row.label(text='Points')
        row.prop(self,'ptcolor_handle_timeA',text='')
        row.prop(self,'ptcolor_handle_timeB',text='')
        row.prop(self,'ptsize_time',text='Point Size')
        row = col.row(align=True)
        #row.label(text='Lines')
        row.prop(self,'lcolor_handle_timeA',text='')
        row.prop(self,'lcolor_handle_timeB',text='')
        row.prop(self,'lsize_time',text='Line Size')

        #box = layout.box()
        col = layout.column(align=True)
        col.label(text='Identity Trail (Path Color - Active Frame Color)')
        row = col.row(align=True)
        row.prop(self,'color_identity_path',text='')
        #row = col.row(align=True)
        row.prop(self,'color_identity_line',text='')
        row.prop(self,'lsize_identity_path',text='')
        #row.prop(settings,'lsize_identity_line',text='')

        
        #box = layout.box()
        col = layout.column(align=True)
        col.label(text='Tracking Points')
        col.label(text='Active Frame Line')
        row = col.row(align=True)
        row.prop(self,'color_tracking_active',text='')
        row.prop(self,'lsize_tracking_active',text='Line Size')
        col.label(text='Path (Prior - Post Frame')
        row = col.row(align=True)
        row.prop(self,'ptcolor_tracking_prior',text='')
        row.prop(self,'ptcolor_tracking_post',text='')
        row.prop(self,'ptsize_tracking',text='Point Size')
        row = col.row(align=True)
        row.prop(self,'lcolor_tracking_prior',text='')
        row.prop(self,'lcolor_tracking_post',text='')
        row.prop(self,'lsize_tracking',text='Line Size')
class DNS_Handle_3DViewDrawHandler:
    #[1/2/20]Question:Q:consider:cleanup: why do I use the DNS? is its use obselete now? Before, I believe I used it when only 1 trail could exist at a time and the DNS was a way to ensure callbacks were cleaned up.
    #but now, since callbacks are cleaned up on file reload anyways and trails don't exist between file reloads, its not necessary?
    def __init__(self,name,callback,args):
        self.name = name
        #In 2.80, depth works with POST_VIEW but not PRE_VIEW, the opposite for 2.79..

        self._handle = bpy.types.SpaceView3D.draw_handler_add(callback, args, 'WINDOW', 'POST_VIEW')
        dns[name] = self 

    def remove_callback(self):
        if self.name in dns:
            instance = dns[self.name]
            bpy.types.SpaceView3D.draw_handler_remove(instance._handle, 'WINDOW')
            del dns[self.name]
            print_time('removed  draw callback from DNS')
        else:
            print_time('cant find DNS  handle {0}!'.format(self.name))

class DNS_Handle_ScenePostUpdate_Trail:
    def __init__(self,target_name,callback):
        
        self.target_name = target_name
        trail_callbacks[target_name] = callback

        
        #instead of using persistent and it's obscure bugs, just let first activated trail add the callback.
        if (TAG_root_ordered_callback not in dns):
            print_time('added scene_update root callback')
            DNS_Handle_ScenePostUpdate(TAG_root_ordered_callback,root_trail_ordered_callback)
        #occurs on file load, DNS exists but handle was removed..
        elif root_trail_ordered_callback not in handlers.depsgraph_update_post:
            print_time('File loaded? added scene_update root callback')
            DNS_Handle_ScenePostUpdate(TAG_root_ordered_callback,root_trail_ordered_callback)

    def remove_callback(self):
        #bugfix: if user tries to change trail preview range using the redo panel, then target name may not be in the callback list
        if self.target_name in trail_callbacks:
            #print(trail_callbacks)
            del trail_callbacks[self.target_name ]
            #print(trail_callbacks)
            reorder_trail_updates()

            #maybe crash occurs due to undoing past a DNS handle add, thus Blender attempts to access a now invalid handle?
            #so maybe removing all handles, even the root callback (if no more trails active) will fix the crash that happens outside of any motion trail and channels trail data call?
            #update:didnt solve it.
            #if len(bpy.context.scene.motion_trail3D_settings.active_trails) == 0:
            #    print_time('last trail deactivated. Removing root callback.')
            #    dns_try_remove_handle(TAG_root_ordered_callback)
            print_time('..removed trail update callback: ' + self.target_name)
            
        else:
            print_time('>>>>WARNING! Possible bug. Trail update handle not removed!')



class DNS_Handle_ScenePostUpdate:
    def __init__(self,name,func):
        self.name = name
        #bugfix: not a reliable index. Other addons may remove from earlier.. hopefully, a bruteforce search is fine
        #self.handle_index = len(handlers.depsgraph_update_post)
        self.func = func 
        handlers.depsgraph_update_post.append(func)
        dns[name] = self 
        
    def remove_callback(self):
        removal_index = -1 
        for i,item in enumerate(handlers.depsgraph_update_post):
            if item == self.func:
                removal_index = i 
                #print('upate pose index found at: ' + str(i)) 
                break 
        if removal_index != -1:
            del handlers.depsgraph_update_post[removal_index]
            #print_time('obscura fixed')
        else: 
            print_time('WARNING!: could not find removal func for scene update post handle in handlers. Will lead to double scene updates(), causing undesirable periodic ctrl snapping which affects graph editor handle selection..')
        if self.name in dns:
            del dns[self.name]
        else:
            print_time("WARNING!: failed to remove func for scene update post handle from DNS.")

TAG_root_ordered_callback = 'root_trail_ordered_callback'

classes =  (Vector4Property,
            Matrix4x4Property,
            DependencyInfo,
            TrailOp,
            StringPropertyWrapper,

            POSE_OT_show_hidden_co,
            POSE_OT_show_hidden_handles,
            POSE_OT_show_hidden_time,
    
            POSE_OT_MotionTrailBeginTag,
            POSE_OT_Deactivate,
            POSE_OT_DeactivateAll,
            POSE_OT_CustomMotionTrail,
            POSE_PT_Custom_Motion_Trail,
            MotionTrail3DSettings,
            POSE_OT_PathToMesh,
            NULL_OT_NULL_OP,
            POSE_OT_CreateAxesTrackingPoints,
            POSE_OT_AddTrackingPoint,
            POSE_OT_ResetTrackingPoint,
            POSE_OT_ClearTrackingPoint,
            POSE_OT_ClearTrackingPoints,
            POSE_OT_MeshFromTrackingPoint,
            POSE_OT_MeshFromTrackingPoints,
            OBJECT_PT_Tracker_Points,
            BONE_PT_Tracker_Points,
            TrackingPoint,
            MotionTrailPreferences,
            MotionTrail3DPropertyObject,
            MotionTrail3DPropertyBone,
            POSE_OT_Flip_Quaternion_Ipo_Direction,
            POSE_PT_Custom_Motion_Trail_Active_Trails,

            )
def register():
    print('-----register motion_trail_3D.py---')
    from bpy.utils import register_class
    for cls in classes:
        register_class(cls)

    global unregistered
    unregistered=False

    bpy.types.Scene.motion_trail3D_settings = PointerProperty(type=MotionTrail3DSettings)
    bpy.types.Object.motion_trail3D = PointerProperty(type=MotionTrail3DPropertyObject)
    bpy.types.PoseBone.motion_trail3D = PointerProperty(type=MotionTrail3DPropertyBone)

    #print('pre count:' + str(len(handlers.depsgraph_update_post)))
    #handlers.depsgraph_update_post.clear()

def unregister():
    
    print('-----unregister motion_trail_3D.py---')
    global unregistered
    unregistered=True
    unregister_handles()

    from bpy.utils import unregister_class
    for cls in classes:
        unregister_class(cls)


    del bpy.types.Scene.motion_trail3D_settings 
    del bpy.types.Object.motion_trail3D
    del bpy.types.PoseBone.motion_trail3D


def dns_try_remove_handle(handle_name):
    #handle object conventionally have remove_handle() func
    if handle_name in dns:
        dns[handle_name].remove_callback()
        #print('properly disposed handle: ' + handle_name)
    else:
        print('WARNING: handle not in dns: ' + handle_name)
        pass
        
def unregister_handles():
    print('unregistering handles')
    dns_try_remove_handle(TAG_root_ordered_callback)

#unregister()
if __name__ == "__main__":
    unregister_handles()
    register()
