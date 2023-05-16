import argparse
import sys
import copy

storages = []


class Variable:
    '''Class for defining CSP variables.

      On initialization the variable object can be given a name and a
      list containing variable's domain of values. You can reset the
      variable's domain if you want to solve a similar problem where
      the domains have changed.

      To support CSP propagation, the class also maintains a current
      domain for the variable. Values pruned from the variable domain
      are removed from the current domain but not from the original
      domain. Values can be also restored.
    '''

    undoDict = dict()             #stores pruned values indexed by a
                                        #(variable,value) reason pair
    def __init__(self, name, domain):
        '''Create a variable object, specifying its name (a
        string) and domain of values.
        '''
        self._name = name                #text name for variable
        self._dom = list(domain)         #Make a copy of passed domain
        self._curdom = list(domain)      #using list
        self._value = None

    def __str__(self):
        return "Variable {}".format(self._name)

    def domain(self):
        '''return copy of variable domain'''
        return(list(self._dom))

    def domainSize(self):
        '''Return the size of the domain'''
        return(len(self.domain()))

    def resetDomain(self, newdomain):
        '''reset the domain of this variable'''
        self._dom = newdomain

    def getValue(self):
        return self._value

    def setValue(self, value):
        if value != None and not value in self._dom:
            print("Error: tried to assign value {} to variable {} that is not in {}'s domain".format(value,self._name,self._name))
        else:
            self._value = value    

    def unAssign(self):
        self.setValue(None)

    def isAssigned(self):
        return self.getValue() != None

    def name(self):
        return self._name

    def curDomain(self):
        '''return copy of variable current domain. But if variable is assigned
           return just its assigned value (this makes implementing hasSupport easier'''
        if self.isAssigned():
            return([self.getValue()])
        return(list(self._curdom))

    def curDomainSize(self):
        '''Return the size of the current domain'''
        if self.isAssigned():
            return(1)
        return(len(self._curdom))

    def inCurDomain(self, value):
        '''check if value is in current domain'''
        if self.isAssigned():
            return(value==self.getValue())
        return(value in self._curdom)

    def pruneValue(self, value, reasonVar, reasonVal):
        '''Remove value from current domain'''
        try:
            self._curdom.remove(value)
        except:
            print("Error: tried to prune value {} from variable {}'s domain, but value not present!".format(value, self._name))
        dkey = (reasonVar, reasonVal)
        if not dkey in Variable.undoDict:
            Variable.undoDict[dkey] = []
        Variable.undoDict[dkey].append((self, value))

    def restoreVal(self, value):
        self._curdom.append(value)

    def restoreCurDomain(self):
        self._curdom = self.domain()

    def reset(self):
        self.restoreCurDomain()
        self.unAssign()

    def dumpVar(self):
        print("Variable\"{}={}\": Dom = {}, CurDom = {}".format(self._name, self._value, self._dom, self._curdom))

    @staticmethod
    def clearUndoDict(self):
        self.undoDict = dict()

    @staticmethod
    def restoreValues(reasonVar, reasonVal):
        dkey = (reasonVar, reasonVal)
        if dkey in Variable.undoDict:
            for (var,val) in Variable.undoDict[dkey]:
                var.restoreVal(val)
            del Variable.undoDict[dkey]



#implement various types of constraints
class Constraint:
    '''Base class for defining constraints. Each constraint can check if
       it has been satisfied, so each type of constraint must be a
       different class. For example a constraint of notEquals(V1,V2)
       must be a different class from a constraint of
       greaterThan(V1,V2), as they must implement different checks of
       satisfaction.

       However one can define a class of general table constraints, as
       below, that can capture many different constraints.

       On initialization the constraint's name can be given as well as
       the constraint's scope. IMPORTANT, the scope is ordered! E.g.,
       the constraint greaterThan(V1,V2) is not the same as the
       contraint greaterThan(V2,V1).
    '''
    def __init__(self, name, scope):
        '''create a constraint object, specify the constraint name (a
        string) and its scope (an ORDERED list of variable
        objects).'''
        self._scope = list(scope)
        self._name = "baseClass_" + name  #override in subconstraint types!

    def scope(self):
        return list(self._scope)

    def arity(self):
        return len(self._scope)

    def numUnassigned(self):
        i = 0
        for var in self._scope:
            if not var.isAssigned():
                i += 1
        return i

    def unAssignedVars(self):
        return [var for var in self.scope() if not var.isAssigned()]

    # def check(self):
    #     util.raiseNotDefined()

    def name(self):
        return self._name

    def __str__(self):
        return "Cnstr_{}({})".format(self.name(), map(lambda var: var.name(), self.scope()))

    def printConstraint(self):
        print("Cons: {} Vars = {}".format(
            self.name(), [v.name() for v in self.scope()]))


#object for holding a constraint problem
class CSP:
    '''CSP class groups together a set of variables and a set of
       constraints to form a CSP problem. Provides a usesful place
       to put some other functions that depend on which variables
       and constraints are active'''

    def __init__(self, name, variables, constraints):
        '''create a CSP problem object passing it a name, a list of
           variable objects, and a list of constraint objects'''
        self._name = name
        self._variables = variables
        self._constraints = constraints

        #some sanity checks
        varsInCnst = set()
        for c in constraints:
            varsInCnst = varsInCnst.union(c.scope())
        for v in variables:
            if v not in varsInCnst:
                print("Warning: variable {} is not in any constraint of the CSP {}".format(v.name(), self.name()))
        for v in varsInCnst:
            if v not in variables:
                print("Error: variable {} appears in constraint but specified as one of the variables of the CSP {}".format(v.name(), self.name()))

        self.constraints_of = [[] for i in range(len(variables))]
        for c in constraints:
            for v in c.scope():
                i = variables.index(v)
                self.constraints_of[i].append(c)

    def name(self):
        return self._name

    def variables(self):
        return list(self._variables)

    def constraints(self):
        return list(self._constraints)

    def constraintsOf(self, var):
        '''return constraints with var in their scope'''
        try:
            i = self.variables().index(var)
            return list(self.constraints_of[i])
        except:
            print("Error: tried to find constraint of variable {} that isn't in this CSP {}".format(var, self.name()))

    def unAssignAllVars(self):
        '''unassign all variables'''
        for v in self.variables():
            v.unAssign()

    def check(self, solutions):
        '''each solution is a list of (var, value) pairs. Check to see
           if these satisfy all the constraints. Return list of
           erroneous solutions'''

        #save values to restore later
        current_values = [(var, var.getValue()) for var in self.variables()]
        errs = []

        for s in solutions:
            s_vars = [var for (var, val) in s]

            if len(s_vars) != len(self.variables()):
                errs.append([s, "Solution has incorrect number of variables in it"])
                continue

            if len(set(s_vars)) != len(self.variables()):
                errs.append([s, "Solution has duplicate variable assignments"])
                continue

            if set(s_vars) != set(self.variables()):
                errs.append([s, "Solution has incorrect variable in it"])
                continue

            for (var, val) in s:
                var.setValue(val)

            for c in self.constraints():
                if not c.check():
                    errs.append([s, "Solution does not satisfy constraint {}".format(c.name())])
                    break

        for (var, val) in current_values:
            var.setValue(val)

        return errs
    
    def __str__(self):
        return "CSP {}".format(self.name())
    

class TableConstraint(Constraint):
    '''General type of constraint that can be use to implement any type of
       constraint. But might require a lot of space to do so.

       A table constraint explicitly stores the set of satisfying
       tuples of assignments.'''

    def __init__(self, name, scope, satisfyingAssignments):
        '''Init by specifying a name and a set variables the constraint is over.
           Along with a list of satisfying assignments.
           Each satisfying assignment is itself a list, of length equal to
           the number of variables in the constraints scope.
           If sa is a single satisfying assignment, e.g, sa=satisfyingAssignments[0]
           then sa[i] is the value that will be assigned to the variable scope[i].


           Example, say you want to specify a constraint alldiff(A,B,C,D) for
           three variables A, B, C each with domain [1,2,3,4]
           Then you would create this constraint using the call
           c = TableConstraint('example', [A,B,C,D],
                               [[1, 2, 3, 4], [1, 2, 4, 3], [1, 3, 2, 4],
                                [1, 3, 4, 2], [1, 4, 2, 3], [1, 4, 3, 2],
                                [2, 1, 3, 4], [2, 1, 4, 3], [2, 3, 1, 4],
                                [2, 3, 4, 1], [2, 4, 1, 3], [2, 4, 3, 1],
                                [3, 1, 2, 4], [3, 1, 4, 2], [3, 2, 1, 4],
                                [3, 2, 4, 1], [3, 4, 1, 2], [3, 4, 2, 1],
                                [4, 1, 2, 3], [4, 1, 3, 2], [4, 2, 1, 3],
                                [4, 2, 3, 1], [4, 3, 1, 2], [4, 3, 2, 1]])
          as these are the only assignments to A,B,C respectively that
          satisfy alldiff(A,B,C,D)
        '''

        Constraint.__init__(self,name, scope)
        self._name = "TableCnstr_" + name
        self.satAssignments = satisfyingAssignments

    def check(self):
        '''check if current variable assignments are in the satisfying set'''
        assignments = []
        for v in self.scope():
            if v.isAssigned():
                assignments.append(v.getValue())
            else:
                return True
        return assignments in self.satAssignments

    def hasSupport(self, var,val):
        '''check if var=val has an extension to an assignment of all variables in
           constraint's scope that satisfies the constraint. Important only to
           examine values in the variable's current domain as possible extensions'''
        if var not in self.scope():
            return True   #var=val has support on any constraint it does not participate in
        vindex = self.scope().index(var)
        found = False
        for assignment in self.satAssignments:
            if assignment[vindex] != val:
                continue   #this assignment can't work it doesn't make var=val
            found = True   #Otherwise it has potential. Assume found until shown otherwise
            for i, v in enumerate(self.scope()):
                if i != vindex and not v.inCurDomain(assignment[i]):
                    found = False  #Bummer...this assignment didn't work it assigns
                    break          #a value to v that is not in v's curDomain
                                   #note we skip checking if val in in var's curDomain
            if found:     #if found still true the assigment worked. We can stop
                break
        return found     #either way found has the right truth value

def findvals(remainingVars, assignment, finalTestfn, partialTestfn=lambda x: True):
    '''Helper function for finding an assignment to the variables of a constraint
       that together with var=val satisfy the constraint. That is, this
       function looks for a supporing tuple.

       findvals uses recursion to build up a complete assignment, one value
       from every variable's current domain, along with var=val.

       It tries all ways of constructing such an assignment (using
       a recursive depth-first search).

       If partialTestfn is supplied, it will use this function to test
       all partial assignments---if the function returns False
       it will terminate trying to grow that assignment.

       It will test all full assignments to "allVars" using finalTestfn
       returning once it finds a full assignment that passes this test.

       returns True if it finds a suitable full assignment, False if none
       exist. (yes we are using an algorithm that is exactly like backtracking!)'''

    # print "==>findvars([",
    # for v in remainingVars: print v.name(), " ",
    # print "], [",
    # for x,y in assignment: print "({}={}) ".format(x.name(),y),
    # print ""

    #sort the variables call the internal version with the variables sorted
    remainingVars.sort(reverse=True, key=lambda v: v.curDomainSize())
    return findvals_(remainingVars, assignment, finalTestfn, partialTestfn)

def findvals_(remainingVars, assignment, finalTestfn, partialTestfn):
    '''findvals_ internal function with remainingVars sorted by the size of
       their current domain'''
    if len(remainingVars) == 0:
        return finalTestfn(assignment)
    var = remainingVars.pop()
    for val in var.curDomain():
        assignment.append((var, val))
        if partialTestfn(assignment):
            if findvals_(remainingVars, assignment, finalTestfn, partialTestfn):
                return True
        assignment.pop()   #(var,val) didn't work since we didn't do the return
    remainingVars.append(var)
    return False


class NValuesConstraint(Constraint):
    '''NValues constraint over a set of variables.  Among the variables in
       the constraint's scope the number that have been assigned
       values in the set 'required_values' is in the range
       [lower_bound, upper_bound] (lower_bound <= #of variables
       assigned 'required_value' <= upper_bound)

       For example, if we have 4 variables V1, V2, V3, V4, each with
       domain [1, 2, 3, 4], then the call
       NValuesConstraint('test_nvalues', [V1, V2, V3, V4], [1,4], 2,
       3) will only be satisfied by assignments such that at least 2
       the V1, V2, V3, V4 are assigned the value 1 or 4, and at most 3
       of them have been assigned the value 1 or 4.

    '''

    def __init__(self, name, scope, required_values, lower_bound, upper_bound):
        Constraint.__init__(self,name, scope)
        self._name = "NValues_" + name
        self._required = required_values
        self._lb = lower_bound
        self._ub = upper_bound

    def check(self):
        assignments = []
        for v in self.scope():
            if v.isAssigned():
                assignments.append(v.getValue())
            else:
                return True
        rv_count = 0

        print("Checking {} with assignments = {}".format(self.name(), assignments))

        for v in assignments:
            if v in self._required:
                rv_count += 1

        print("rv_count = {} test = {}".format(rv_count, self._lb <= rv_count and self._ub >= rv_count))


        return self._lb <= rv_count and self._ub >= rv_count

    def hasSupport(self, var, val):
        '''check if var=val has an extension to an assignment of the
           other variable in the constraint that satisfies the constraint

           HINT: check the implementation of AllDiffConstraint.hasSupport
                 a similar approach is applicable here (but of course
                 there are other ways as well)
        '''
        if var not in self.scope():
            return True   #var=val has support on any constraint it does not participate in

        #define the test functions for findvals
        def valsOK(l):
            '''tests a list of assignments which are pairs (var,val)
               to see if they can satisfy this sum constraint'''
            rv_count = 0
            vals = [val for (var, val) in l]
            for v in vals:
                if v in self._required:
                    rv_count += 1
            least = rv_count + self.arity() - len(vals)
            most =  rv_count
            return self._lb <= least and self._ub >= most
        varsToAssign = self.scope()
        varsToAssign.remove(var)
        x = findvals(varsToAssign, [(var, val)], valsOK, valsOK)
        return x

class IfAllThenOneConstraint(Constraint):
    '''if each variable in left_side equals each value in left_values 
    then one of the variables in right side has to equal one of the values in right_values. 
    hasSupport tested only, check() untested.'''
    def __init__(self, name, left_side, right_side, left_values, right_values):
        Constraint.__init__(self,name, left_side+right_side)
        self._name = "IfAllThenOne_" + name
        self._ls = left_side
        self._rs = right_side
        self._lv = left_values
        self._rv = right_values



def parse_input_file(filepath):
    ###################################################
    ## Parse the input file and generate constraints,
    ## and the game board.
    ## checking errors completed.
    ###################################################
    with open(filepath, 'r') as f:
        row_constraints = [int(x) for x in f.readline().strip()]
        col_constraints = [int(x) for x in f.readline().strip()]
        num_ships = [int(x) for x in f.readline().strip()]
        grid = []
        for line in f:
            row = [c for c in line.strip()]
            grid.append(row)
    
    return row_constraints, col_constraints, num_ships, grid

def create_variables(grid):
    ###################################################
    ## Parse the input file and generate constraints,
    ## and the game board.
    ## In my game, i choose each grid box as a variable.
    ## In total, it will have 36 variables.
    ## checking errors completed.
    ###################################################
    grid_length = len(grid)
    stored_variables = {}
    unassignedVars = []
    ## remember: i is the row number of the grid, j is the column number.
    for i in range(grid_length):
        for j in range(grid_length):
            if grid[i][j] == '0': ## this means the gird is empty. Yes!
                name = str(i*grid_length+j)
                var = Variable(name, ['S', '.', '<', '>', '^', 'v', 'M'])
            else: ## this means the grid is not empty. The domain should be itself.
                name = str(i*grid_length+j)
                var = Variable(name, grid[i][j])
            stored_variables[name] = var
            unassignedVars.append(var)

    ## In the return statement, unassigned variables are used in below GAC Algo.
    ## Stored variables are used to generate constraints.
    return unassignedVars, stored_variables

def corner(grid, row, column, stored_variables):
    ###################################################
    ## Form constraints for 4 corners of the grid.
    ## At each corner, the constraints are slightly different.
    ## In total, it will have 12 constraints at each corner.
    ## Checking errors completed. Mainly focus on possible values.
    ###################################################
    constraint_list = []
    length = len(grid)
    if row == column and row == 0:
        # for c1, define the up and down boxes.
        c1_name = f"surround_{row}_{column}_to_{row + 1}_{column}"
        c1_scope = [stored_variables[str(row*length+column)], 
                    stored_variables[str((row + 1)*length+column)]]
        c1 = TableConstraint(c1_name, c1_scope, [['S', '.'], ['.', 'S'], ['.', '^'], ['^', 'v'], ['^', 'M'], ['<', '.'], ['.', '<'], ['.', '.']])
        # for c2, define the left and right boxes.
        c2_name = f"surround_{row}_{column}_to_{row}_{column + 1}"
        c2_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str(row*length+column + 1)]]
        c2 = TableConstraint(c2_name, c2_scope, [['.', '.'], ['.', 'S'], ['S', '.'], ['.', '<'], ['<', '>'], ['^', '.'], ['.', '^'], ['<', 'M']])
        # for c3, define the rightmost and leftmost boxes.
        c3_name = f"surround_{row}_{column}_to_{row+1}_{column + 1}"
        c3_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str((row + 1)*length+column + 1)]]
        c3 = TableConstraint(c3_name, c3_scope, [['.', '.'], ['.', 'S'], ['.', '<'], ['.', '>'], ['.', '^'], ['.', 'v'], ['.', 'M'], ['S', '.'], ['<', '.'], ['^', '.']])
        constraint_list.append(c1)
        constraint_list.append(c2)
        constraint_list.append(c3)
    if row == column and row == length - 1:
        # c4 is bottom and left boxes.
        c4_name = f"surround_{row}_{column}_to_{row}_{column - 1}"
        c4_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str(row*length+column - 1)]]
        c4 = TableConstraint(c4_name, c4_scope, [['.', '.'], ['.', '>'], ['.', 'v'], ['.', 'S'], ['>', '<'], ['>', 'M'], ['v', '.'], ['S', '.']])
        # c5 is bottom and up boxes.
        c5_name = f"surround_{row}_{column}_to_{row - 1}_{column}"
        c5_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str((row - 1)*length+column)]]
        c5 = TableConstraint(c5_name, c5_scope, [['.', '.'], ['.', '>'], ['.', 'v'], ['.', 'S'], ['S', '.'], ['>', '.'], ['v', '^'], ['v', 'M']])
        # c6 is bottom and its diagonal left boxes.
        c6_name = f"surround_{row}_{column}_to_{row - 1}_{column - 1}"
        c6_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str((row - 1)*length+column - 1)]]
        c6 = TableConstraint(c6_name, c6_scope, [['.', '.'], ['.', '<'], ['.', '>'], ['.', 'v'], ['.', '^'], ['.', 'S'], ['.', 'M'], ['S', '.'], ['>', '.'], ['v', '.']])
        constraint_list.append(c4)
        constraint_list.append(c5)
        constraint_list.append(c6)
    if row == length - 1 and column == 0:
        # c7 is the left-most and down-most box with its right box.
        c7_name = f"surround_{row}_{column}_to_{row}_{column + 1}"
        c7_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str(row*length+column + 1)]]
        c7 = TableConstraint(c7_name, c7_scope, [['.', '.'], ['.', 'S'], ['.', 'v'], ['.', '<'], ['<', '>'], ['<', 'M'], ['S', '.'], ['v', '.']])
        # c8 is with its upper box.
        c8_name = f"surround_{row}_{column}_to_{row - 1}_{column}"
        c8_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str((row - 1)*length+column)]]
        c8 = TableConstraint(c8_name, c8_scope, [['.', '.'], ['.', 'S'], ['.', 'v'], ['.', '<'], ['<', '.'], ['v', '^'], ['S', '.'], ['v', 'M']])
        # c9 is with its diagonal box.
        c9_name = f"surround_{row}_{column}_to_{row - 1}_{column + 1}"
        c9_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str((row - 1)*length+column + 1)]]
        c9 = TableConstraint(c9_name, c9_scope, [['.', '.'], ['.', 'S'], ['.', 'v'], ['.', '<'], ['.', '^'], ['.', 'M'], ['.', '>'], ['S', '.'], ['<', '.'], ['v', '.']])
        constraint_list.append(c7)
        constraint_list.append(c8)
        constraint_list.append(c9)
    if row == 0 and column == length - 1:
        c10_name = f"surround_{row}_{column}_to_{row}_{column - 1}"
        c10_scope = [stored_variables[str(row*length+column)],
                     stored_variables[str(row*length+column - 1)]]
        c10 = TableConstraint(c10_name, c10_scope, [['.', '.'], ['.', 'S'], ['.', '^'], ['.', '>'], ['>', '<'], ['S', '.'], ['>', 'M'], ['^', '.']])
        c11_name = f"surround_{row}_{column}_to_{row + 1}_{column}"
        c11_scope = [stored_variables[str(row*length+column)],
                     stored_variables[str((row + 1)*length+column)]]
        c11 = TableConstraint(c11_name, c11_scope, [['.', '.'], ['.', 'S'], ['.', '^'], ['.', '>'], ['S', '.'], ['>', '.'], ['^', 'v'], ['^', 'M']])
        c12_name = f"surround_{row}_{column}_to_{row + 1}_{column - 1}"
        c12_scope = [stored_variables[str(row*length+column)],
                     stored_variables[str((row + 1)*length+column - 1)]]
        c12 = TableConstraint(c12_name, c12_scope, [['.', '.'], ['.', 'S'], ['.', '^'], ['.', '>'], ['.', 'v'], ['.', '<'], ['.', 'M'], ['S', '.'], ['>', '.'], ['^', '.']])
        constraint_list.append(c10)
        constraint_list.append(c11)
        constraint_list.append(c12)
    
    return constraint_list

def sides(grid, row, column, stored_variables):
    #################################################################################
    ## Form constraints for 4 sides of the chessboard.
    ## At each sides, the constraints are slightly different.
    ## At each grid box on the side, there are 5 constraints for each box.
    ## Remember we do not consider each corner since we have already considered them.
    ## The number of constraints cannot be considered since it depends on the grid.
    ## There will be 80 sides constraints for 6x6 grid.
    ## Checking errors completed. Mainly focus on possible values.
    #################################################################################
    constraint_list = []
    length = len(grid)
    if row != 0 and row != length - 1 and column == 0:
        ## leftmost column and its down.
        c1_name = f"surround_{row}_{column}_to_{row + 1}_{column}"
        c1_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str((row + 1)*length+column)]]
        c1 = TableConstraint(c1_name, c1_scope, [['.', '.'], ['.', 'S'], ['.', '^'], ['.', '<'], ['S', '.'], ['M', 'v'], ['M', 'M'], ['^', 'v'], ['^', 'M'], ['v', '.'], ['<', '.']])
        ## leftmost and its right. 
        c2_name = f"surround_{row}_{column}_to_{row}_{column + 1}"
        c2_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str(row*length+column + 1)]]
        c2 = TableConstraint(c2_name, c2_scope, [['.', '.'], ['.', 'S'], ['.', '<'], ['.', '^'], ['.', 'v'], ['.', 'M'], ['S', '.'], ['M', '.'], ['<', '>'], ['<', 'M'], ['^', '.'], ['v', '.']])
        ## leftmost and its up.
        c3_name = f"surround_{row}_{column}_to_{row - 1}_{column}"
        c3_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str((row - 1)*length+column)]]
        c3 = TableConstraint(c3_name, c3_scope, [['.', '.'], ['.', 'S'], ['.', '<'], ['.', 'v'], ['S', '.'], ['M', 'M'], ['M', '^'], ['^', '.'], ['v', '^'], ['v', 'M'], ['<', '.']])
        ## leftmost and its diagonal up.
        c4_name = f"surround_{row}_{column}_to_{row - 1}_{column + 1}"
        c4_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str((row - 1)*length+column + 1)]]
        c4 = TableConstraint(c4_name, c4_scope, [['.', '.'], ['.', 'S'], ['.', '^'], ['.', 'v'], ['.', '<'], ['.', '>'], ['.', 'M'], ['S', '.'], ['M', '.'], ['<', '.'], ['^', '.'], ['v', '.']])
        ## leftmost and its diagonal down.
        c5_name = f"surround_{row}_{column}_to_{row + 1}_{column + 1}"
        c5_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str((row + 1)*length+column + 1)]]
        c5 = TableConstraint(c5_name, c5_scope, [['.', '.'], ['.', 'S'], ['.', '^'], ['.', 'v'], ['.', '<'], ['.', '>'], ['.', 'M'], ['S', '.'], ['M', '.'], ['<', '.'], ['^', '.'], ['v', '.']])
        constraint_list.append(c1)
        constraint_list.append(c2)
        constraint_list.append(c3)
        constraint_list.append(c4)
        constraint_list.append(c5)
    if row != 0 and row != length - 1 and column == length - 1:
        ## rightmost column and its down
        c6_name = f"surround_{row}_{column}_to_{row + 1}_{column}"
        c6_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str((row + 1)*length+column)]]
        c6 = TableConstraint(c6_name, c6_scope, [['.', '.'], ['.', '^'], ['.', 'S'], ['.', '>'], ['S', '.'], ['M', 'v'], ['M', 'M'], ['^', 'M'], ['^', 'v'], ['v', '.'], ['>', '.']])
        ## rightmost column and its up
        c7_name = f"surround_{row}_{column}_to_{row - 1}_{column}"
        c7_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str((row - 1)*length+column)]]
        c7 = TableConstraint(c7_name, c7_scope, [['.', '.'], ['.', 'S'], ['.', '>'], ['.', 'v'], ['S', '.'], ['M', 'M'], ['M', '^'], ['^', '.'], ['v', '^'], ['v', 'M'], ['>', '.']])
        ## rightmost column and its left
        c8_name = f"surround_{row}_{column}_to_{row}_{column - 1}"
        c8_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str(row*length+column - 1)]]
        c8 = TableConstraint(c8_name, c8_scope, [['.', '.'], ['.', 'S'], ['.', '>'], ['.', 'v'], ['.', '^'], ['.', 'M'], ['S', '.'], ['M', '.'], ['>', '<'], ['>', 'M'], ['^', '.'], ['v', '.']])
        ## rightmost column and its diagonal up.
        c9_name = f"surround_{row}_{column}_to_{row - 1}_{column - 1}"
        c9_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str((row - 1)*length+column - 1)]]
        c9 = TableConstraint(c9_name, c9_scope, [['.', '.'], ['.', 'S'], ['.', 'M'], ['.', 'v'], ['.', '^'], ['.', '<'], ['.', '>'], ['S', '.'], ['M', '.'], ['>', '.'], ['^', '.'], ['v', '.']])
        ## rightmost column and its diagonal down.
        c10_name = f"surround_{row}_{column}_to_{row + 1}_{column - 1}"
        c10_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str((row + 1)*length+column - 1)]]
        c10 = TableConstraint(c10_name, c10_scope, [['.', '.'], ['.', 'S'], ['.', 'M'], ['.', 'v'], ['.', '^'], ['.', '<'], ['.', '>'], ['S', '.'], ['M', '.'], ['>', '.'], ['^', '.'], ['v', '.']])
        constraint_list.append(c6)
        constraint_list.append(c7)
        constraint_list.append(c8)
        constraint_list.append(c9)
        constraint_list.append(c10)
    if column != 0 and column != length - 1 and row == 0:
        ## upmost row and its right 
        c11_name = f"surround_{row}_{column}_to_{row}_{column + 1}"
        c11_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str(row*length+column + 1)]]
        c11 = TableConstraint(c11_name, c11_scope, [['.', '.'], ['.', 'S'], ['.', '^'], ['.', '<'], ['S', '.'], ['M', '>'], ['M', 'M'], ['^', '.'], ['<', '>'], ['<', 'M'], ['>', '.']])
        ## upmost row and its left.
        c12_name = f"surround_{row}_{column}_to_{row}_{column - 1}"
        c12_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str(row*length+column - 1)]]
        c12 = TableConstraint(c12_name, c12_scope, [['.', '.'], ['.', 'S'], ['.', '^'], ['.', '>'], ['S', '.'], ['M', '<'], ['M', 'M'], ['>', '<'], ['>', 'M'], ['^', '.'], ['<', '.']])
        ## upmost row and its down.
        c13_name = f"surround_{row}_{column}_to_{row + 1}_{column}"
        c13_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str((row + 1)*length+column)]]
        c13 = TableConstraint(c13_name, c13_scope, [['.', '.'], ['.', 'S'], ['.', 'M'], ['.', '^'], ['.', '>'], ['.', '<'], ['S', '.'], ['M', '.'], ['>', '.'], ['^', 'v'], ['^', 'M'], ['<', '.']])
        ## upmost row and its diagonal right
        c14_name = f"surround_{row}_{column}_to_{row + 1}_{column + 1}"
        c14_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str((row + 1)*length+column + 1)]]
        c14 = TableConstraint(c14_name, c14_scope, [['.', '.'], ['.', 'S'], ['.', 'M'], ['.', '<'], ['.', '>'], ['.', '^'], ['.', 'v'], ['S', '.'], ['M', '.'], ['<', '.'], ['>', '.'], ['^', '.']])
        ## upmost row and its diagonal left.
        c15_name = f"surround_{row}_{column}_to_{row + 1}_{column - 1}"
        c15_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str((row + 1)*length+column - 1)]]
        c15 = TableConstraint(c15_name, c15_scope, [['.', '.'], ['.', 'S'], ['.', 'M'], ['.', '<'], ['.', '>'], ['.', '^'], ['.', 'v'], ['S', '.'], ['M', '.'], ['<', '.'], ['>', '.'], ['^', '.']])
        constraint_list.append(c11)
        constraint_list.append(c12)
        constraint_list.append(c13)
        constraint_list.append(c14)
        constraint_list.append(c15)
    if column != 0 and column != length - 1 and row == length - 1:
        ## downmost row and its right
        c16_name = f"surround_{row}_{column}_to_{row}_{column + 1}"
        c16_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str(row*length+column + 1)]]
        c16 = TableConstraint(c16_name, c16_scope, [['.', '.'], ['.', 'S'], ['.', '<'], ['.', 'v'], ['S', '.'], ['M', 'M'], ['M', '>'], ['<', 'M'], ['<', '>'], ['>', '.'], ['v', '.']])
        ## downmost row and its left
        c17_name = f"surround_{row}_{column}_to_{row}_{column - 1}"
        c17_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str(row*length+column - 1)]]
        c17 = TableConstraint(c17_name, c17_scope, [['.', '.'], ['.', 'S'], ['.', '>'], ['.', 'v'], ['S', '.'], ['M', '<'], ['M', 'M'], ['<', '.'], ['>', '<'], ['>', 'M'], ['v', '.']])
        ## downmost row and its up
        c18_name = f"surround_{row}_{column}_to_{row - 1}_{column}"
        c18_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str((row - 1)*length+column)]]
        c18 = TableConstraint(c18_name, c18_scope, [['.', '.'], ['.', 'S'], ['.', 'M'], ['.', '<'], ['.', '>'], ['.', 'v'], ['S', '.'], ['M', '.'], ['>', '.'], ['<', '.'], ['v', '^'], ['v', 'M']])
        ## downmost row and its diagonal right
        c19_name = f"surround_{row}_{column}_to_{row - 1}_{column + 1}"
        c19_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str((row - 1)*length+column + 1)]]
        c19 = TableConstraint(c19_name, c19_scope, [['.', '.'], ['.', 'S'], ['.', 'M'], ['.', '<'], ['.', '>'], ['.', '^'], ['.', 'v'], ['S', '.'], ['M', '.'], ['<', '.'], ['>', '.'], ['v', '.']])
        ## downmost row and its diagonal left
        c20_name = f"surround_{row}_{column}_to_{row - 1}_{column - 1}"
        c20_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str((row - 1)*length+column - 1)]]
        c20 = TableConstraint(c20_name, c20_scope, [['.', '.'], ['.', 'S'], ['.', 'M'], ['.', '<'], ['.', '>'], ['.', '^'], ['.', 'v'], ['S', '.'], ['M', '.'], ['<', '.'], ['>', '.'], ['v', '.']])
        constraint_list.append(c16)
        constraint_list.append(c17)
        constraint_list.append(c18)
        constraint_list.append(c19)
        constraint_list.append(c20)
    
    return constraint_list

        
def non_sides(grid, row, column, stored_variables):
    #################################################################################
    ## Form constraints for the inner (except 4 sides) of the chessboard.
    ## At each box, the constraints are slightly different. (mainly on the second layer of the board)
    ## there are 8 constraints for each box.
    ## Remember we do not consider each corner and sides since we have already considered them.
    ## The number of constraints cannot be considered since it depends on the grid.
    ## There will be 128 non-sides constraints for 6x6 grid.
    ## Checking errors completed. Mainly focus on possible values.
    #################################################################################
    constraint_list = []
    length = len(grid)
    if column != 0 and column != length - 1 and row != 0 and row != length - 1:
        ## general cases for each pieces.
        ## for chess up.
        c1_name = f"surround_{row}_{column}_to_{row - 1}_{column}"
        c1_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str((row - 1)*length+column)]]
        c1 = TableConstraint(c1_name, c1_scope, [['.', '.'], ['.', 'S'], ['.', 'M'], ['.', '>'], ['.', '<'], ['.', 'v'], ['S', '.'], ['M', '.'], ['M', 'M'], ['M', '^'], ['^', '.'], ['v', '^'], ['v', 'M'], ['>', '.'], ['<', '.']])
        if row == 1:
            c1.satAssignments.remove(['.', 'v'])
            c1.satAssignments.remove(['v', 'M'])
            c1.satAssignments.remove(['M', 'M'])
        ## for chess down
        c2_name = f"surround_{row}_{column}_to_{row + 1}_{column}"
        c2_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str((row + 1)*length+column)]]
        c2 = TableConstraint(c2_name, c2_scope, [['.', '.'], ['.', 'S'], ['.', 'M'], ['.', '^'], ['.', '>'], ['.', '<'], ['S', '.'], ['M', '.'], ['M', 'M'], ['M', 'v'], ['^', 'M'], ['^', 'v'], ['v', '.'], ['<', '.'], ['>', '.']])
        if row == length - 2:
            c2.satAssignments.remove(['.', '^'])
            c2.satAssignments.remove(['M', 'M'])
            c2.satAssignments.remove(['^', 'M'])
        ## chess left
        c3_name = f"surround_{row}_{column}_to_{row}_{column - 1}"
        c3_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str(row*length+column - 1)]]
        c3 = TableConstraint(c3_name, c3_scope, [['.', '.'], ['.', 'S'], ['.', 'M'], ['.', '>'], ['.', '^'], ['.', 'v'], ['S', '.'], ['M', '.'], ['M', '<'], ['M', 'M'], ['<', '.'], ['>', 'M'], ['>', '<'], ['^', '.'], ['v', '.']])
        if column == 1:
            c3.satAssignments.remove(['.', '>'])
            c3.satAssignments.remove(['>', 'M'])
            c3.satAssignments.remove(['M', 'M'])
        ## chess right
        c4_name = f"surround_{row}_{column}_to_{row}_{column + 1}"
        c4_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str(row*length+column + 1)]]
        c4 = TableConstraint(c4_name, c4_scope, [['.', '.'], ['.', 'S'], ['.', 'M'], ['.', '^'], ['.', 'v'], ['.', '<'], ['S', '.'], ['M', '.'], ['M', '>'], ['M', 'M'], ['>', '.'], ['<', 'M'], ['<', '>'], ['^', '.'], ['v', '.']])
        if column == length - 2:
            c4.satAssignments.remove(['.', '<'])
            c4.satAssignments.remove(['<', 'M'])
            c4.satAssignments.remove(['M', 'M'])
        ## diagonal up left
        c5_name = f"surround_{row}_{column}_to_{row - 1}_{column - 1}"
        c5_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str((row - 1)*length+column - 1)]]
        c5 = TableConstraint(c5_name, c5_scope, [['.', '.'], ['.', 'S'], ['.', 'M'], ['.', '>'], ['.', '<'], ['.', '^'], ['.', 'v'], ['S', '.'], ['M', '.'], ['>', '.'], ['<', '.'], ['^', '.'], ['v', '.']])
        if row == 1 and column == 1:
            c5.satAssignments.remove(['.', '>'])
            c5.satAssignments.remove(['.', 'v'])
            c5.satAssignments.remove(['.', 'M'])
        ## diagonal up right
        c6_name = f"surround_{row}_{column}_to_{row - 1}_{column + 1}"
        c6_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str((row - 1)*length+column + 1)]]
        c6 = TableConstraint(c6_name, c6_scope, [['.', '.'], ['.', 'S'], ['.', 'M'], ['.', '>'], ['.', '<'], ['.', '^'], ['.', 'v'], ['S', '.'], ['M', '.'], ['>', '.'], ['<', '.'], ['^', '.'], ['v', '.']])
        if row == 1 and column == length - 2:
            c6.satAssignments.remove(['.', '<'])
            c6.satAssignments.remove(['.', 'v'])
            c6.satAssignments.remove(['.', 'M'])
        ## diagonal down left
        c7_name = f"surround_{row}_{column}_to_{row + 1}_{column - 1}"
        c7_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str((row + 1)*length+column - 1)]]
        c7 = TableConstraint(c7_name, c7_scope, [['.', '.'], ['.', 'S'], ['.', 'M'], ['.', '>'], ['.', '<'], ['.', '^'], ['.', 'v'], ['S', '.'], ['M', '.'], ['>', '.'], ['<', '.'], ['^', '.'], ['v', '.']])
        if row == length - 2 and column == 1:
            c7.satAssignments.remove(['.', '^'])
            c7.satAssignments.remove(['.', '>'])
            c7.satAssignments.remove(['.', 'M'])
        ## diagonal down right
        c8_name = f"surround_{row}_{column}_to_{row + 1}_{column + 1}"
        c8_scope = [stored_variables[str(row*length+column)],
                    stored_variables[str((row + 1)*length+column + 1)]]
        c8 = TableConstraint(c8_name, c8_scope, [['.', '.'], ['.', 'S'], ['.', 'M'], ['.', '>'], ['.', '<'], ['.', '^'], ['.', 'v'], ['S', '.'], ['M', '.'], ['>', '.'], ['<', '.'], ['^', '.'], ['v', '.']])
        if row == length - 2 and column == length - 2:
            c8.satAssignments.remove(['.', '^'])
            c8.satAssignments.remove(['.', '<'])
            c8.satAssignments.remove(['.', 'M'])

        constraint_list.append(c1)
        constraint_list.append(c2)
        constraint_list.append(c3)
        constraint_list.append(c4)
        constraint_list.append(c5)
        constraint_list.append(c6)
        constraint_list.append(c7)
        constraint_list.append(c8)

    return constraint_list


def create_constraints(grid, row_constraints, col_constraints, stored_variables):
    #################################################################################
    ## Create constraints based on the stored variables and each constraints.
    ## This function will form constraints for each box in the grid and create row and column constraints
    ## based on the input file's row and column constraints.
    #################################################################################
    grid_length = len(grid)
    stored_constraints = []
    ## this may be different: we want to define row i and column i together.
    for i in range(grid_length):
        ## following parts are used to create the table constraints for each grid box.
        row_var, col_var = [], []
        for j in range(grid_length):
            row_name = str(i*grid_length+j)
            col_name = str(i+j*grid_length)
            row_var.append(stored_variables[row_name])
            col_var.append(stored_variables[col_name])
            
            stored_constraints += corner(grid, i, j, stored_variables)
            stored_constraints += sides(grid, i, j, stored_variables)
            stored_constraints += non_sides(grid, i, j, stored_variables)
        
        ## following parts are used to create the row and column constraints using Nvalues.
        ## remember that when the top row, we cannot have 'v', when the left-most column, we cannot have '>'
        if i == 0:
            row_parts = ['S', '<', '>', '^', 'M']
            col_parts = ['S', '<', '^', 'v', 'M']
            stored_constraints.append(NValuesConstraint(f'row_{i}', row_var, row_parts, row_constraints[i], row_constraints[i]))
            stored_constraints.append(NValuesConstraint(f'column_{i}', col_var, col_parts, col_constraints[i], col_constraints[i]))
        ## remember that when the bottom row, we cannot have '^', when the right-most column, we cannot have '<'
        if i == grid_length - 1:
            row_parts = ['S', '<', '>', 'v', 'M']
            col_parts = ['S', '>', '^', 'v', 'M']
            stored_constraints.append(NValuesConstraint(f'row_{i}', row_var, row_parts, row_constraints[i], row_constraints[i]))
            stored_constraints.append(NValuesConstraint(f'column_{i}', col_var, col_parts, col_constraints[i], col_constraints[i]))
        ## finally, form the Nvalues constraints for the general rows and columns.
        if i != grid_length - 1 and i != 0:
            general_parts = ['S', '<', '>', '^', 'v', 'M']
            stored_constraints.append(NValuesConstraint(f'row_{i}', row_var, general_parts, row_constraints[i], row_constraints[i]))
            stored_constraints.append(NValuesConstraint(f'column_{i}', col_var, general_parts, col_constraints[i], col_constraints[i]))

    return stored_constraints


def place_and_check_result(ship_constraints, csp, length):
    ########################################################################
    ## This function is called to validate the result our csp generates.
    ## First we generate the solution and check whether the battleship places correctly.
    ## Then we check whether the ship constraints are satisfied.
    ## Finally we place the solution to our global variable SOLUTION
    ## checking error completes. --> a reminder for myself. P.S. So difficult to debug.
    ########################################################################

    ## create a length*length grid to store the result.
    result = [[j for j in range(length)] for i in range(length)]
    ## store the variable's value in this solution:
    for var in csp.variables():
        name = var.name()
        grid_num = int(name)
        row_index = grid_num // len(grid)
        col_index = grid_num % len(grid)
        result[row_index][col_index] = var.getValue()
    # print(result)
    ## there are serveral ship types: check whether the solution is correct.
    for i in range(1, length - 1):
        for j in range(1, length - 1):
            ## at this stage, check the ship contains 'M'
            if result[i][j] == 'M':
                # verticle ship. this only can be ^ or ^ .
                #                                 M    M
                #                                 v    M
                #                                      v
                if result[i - 1][j] in ['^', 'M'] and result[i + 1][j] in ['M', 'v'] and result[i][j + 1] == result[i][j - 1] and result[i][j + 1] == '.':
                    # this will check we do not contains the ship which its length is 5.
                    if result[i - 1][j] == 'M' and result[i + 1][j] != 'v':
                        # print('exit at 1')
                        return 'invalid'
                    if result[i + 1][j] == 'M' and result[i - 1][j] != '^':
                        # print('exit at 2')
                        return 'invalid'
                if (result[i - 1][j] not in ['^', 'M'] or result[i + 1][j] not in ['M', 'v']) and result[i][j + 1] == result[i][j - 1] and result[i][j + 1] == '.':
                    return 'invalid'
                # horizontal ship. this only can be < M > or < M M >. 
                # Also remember this length also should not be 5.
                if result[i][j - 1] in ['M', '<'] and result[i][j + 1] in ['M', '>'] and result[i + 1][j] == result[i - 1][j] and result[i + 1][j] == '.':
                    if result[i][j - 1] == 'M' and result[i][j + 1] != '>':
                        # print('exit at 4')
                        return 'invalid'
                    if result[i][j + 1] == 'M' and result[i][j - 1] != '<':
                        # print('exit at 5')
                        return 'invalid'
                if (result[i][j - 1] not in ['M', '<'] or result[i][j + 1] not in ['M', '>']) and result[i + 1][j] == result[i - 1][j] and result[i + 1][j] == '.':
                    return 'invalid'

    # print('next part')
    # Let's check the number of the ship.
    submarines, subnum = ship_constraints[0], 0
    destroyers, desnum = ship_constraints[1], 0
    cruisers, crunum = ship_constraints[2], 0
    battleships, batnum = ship_constraints[3], 0
    water_num = 0

    for i in range(length):
        for j in range(length):
            if result[i][j] == '.': # avoiding the index out of range .....
                water_num += 1
            elif result[i][j] == 'S': # this is submarine
                subnum += 1
            elif result[i][j] == '^' and result[i + 1][j] == 'v':
                desnum += 1
            elif result[i][j] == '<' and result[i][j + 1] == '>':
                desnum += 1
            elif result[i - 1][j] == '^' and result[i][j] == 'M' and result[i + 1][j] == 'v':
                crunum += 1
            elif result[i][j - 1] == '<' and result[i][j] == 'M' and result[i][j + 1] == '>':
                crunum += 1
            elif result[i][j] == 'M' and result[i][j - 1] == 'M' and result[i][j + 1] == '>':
                batnum += 1
            elif result[i][j] == 'M' and result[i - 1][j] == 'M' and result[i + 1][j] == 'v':
                batnum += 1
    
    ## check whether satisfies the ship number constraints.
    if subnum > submarines or desnum > destroyers or crunum > cruisers or batnum > battleships:
        return 'invalid'
    # print([subnum, desnum, crunum, batnum])

    ## after checking the constariants. append this result to our localStorage. We will check it at the end.
    storages.append(result)
    return 'valid'
    

def GacEnforce(csp, constraints, assignedvar, assignedval):
    ## This function is for helping on AC-3 algorithm to find the solution.
    ## Borrow idea from instructor's post on Piazza.
    ## checking error completes. --> a reminder for myself. P.S. So difficult to debug.
    while not constraints == []:
        cons = constraints.pop(0)
        for var in cons.scope():
            for val in var.curDomain():
                if not cons.hasSupport(var, val):
                    # print(var.curDomain())
                    var.pruneValue(val, assignedvar, assignedval)
                    if var.curDomainSize() == 0:
                        return 'OWO' # cute.
                    for recheck in csp.constraintsOf(var):
                        if recheck != cons and not recheck in constraints:
                            constraints.append(recheck)
    return 'OK'


def GAC(unAssignedVars, ship_constraints, csp, length):
    ## This function is for performing AC-3 algorithm to find the solution.
    ## Borrow idea from instructor's post on Piazza.
    ## checking error completes. --> a reminder for myself. P.S. So difficult to debug.
    if unAssignedVars == []:
        place_and_check_result(ship_constraints, csp, length)
        return 'OK'
    var = unAssignedVars.pop(0)
    for val in var.curDomain():
        var.setValue(val)
        noOWO = True
        if GacEnforce(csp, csp.constraintsOf(var), var, val) == 'OWO':
            noOWO = False
        if noOWO:
            GAC(unAssignedVars, ship_constraints, csp, length)
        Variable.restoreValues(var, val)
    var.setValue(None)
    unAssignedVars.append(var)
    return 


def convert_result_to_str(solution):
    length = len(solution)
    result_strings = ""
    for i in range(length):
        j = 0
        while j < length:
            result_strings += str(solution[i][j])
            j += 1
        result_strings += "\n"

    return result_strings


def print_solution(filename, solution):
    file = open(filename, 'w')
    file.write(convert_result_to_str(solution))
    file.close()


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--inputfile",
        type=str,
        required=True,
        help="The input file that contains the battleship puzzle."
    )
    parser.add_argument(
        "--outputfile",
        type=str,
        required=True,
        help="The output file that contains the solution of battleship puzzle."
    )
    args = parser.parse_args()

    row_constraints, col_constraints, num_ships, grid = parse_input_file(args.inputfile)
    ## following lines are used to check if the input file reads correctly. for testing purpose,
    ## commented out these four lines.
    # print(row_constraints)
    # print(col_constraints)
    # print(num_ships)
    # print(grid)

    ## following lines are used to check if the create variable function is working. for testing purpose,
    var_list, var_dict = create_variables(grid)
    # for var in var_list:
    #     print(var.domain())
    # print(len(var_list)) ## in easy should be 36.
    # print(var_dict)

    ## following lines are used to check if the create constraint function is working. for testing purpose,
    constraint_list = create_constraints(grid, row_constraints, col_constraints, var_dict)
    # print(len(constraint_list)) # the constraints number should be 232. Row and Column are 16 and Table should be 220.

    # every time run into this process, remember to clean the global variables
    storages = []

    # begin this game!
    length = len(row_constraints)
    csp = CSP('game', var_list, constraint_list)
    GAC(CSP.variables(csp), num_ships, csp, length)
    # print(storages)
    print_solution(args.outputfile, storages[-1])


