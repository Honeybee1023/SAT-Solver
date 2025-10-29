"""
6.101 Lab:
SAT Solver
"""

#!/usr/bin/env python3

# import typing  # optional import
# import pprint  # optional import
import doctest
import sys

sys.setrecursionlimit(10_000)
# NO ADDITIONAL IMPORTS


def update_formula(formula, var, value):
    """
    Update the formula given a variable assignment.

    formula: a CNF formula
    var: a variable (string)
    value: a Boolean value

    Returns: a new formula, simplified according to the assignment of var to
        value. Does not mutate input formula.
    """
    # Instead of deleting stuff from copy of original formula,
    # select remaining things to put in new copy as we go
    # This way we save time of making a full copy
    new_formula = []
    for clause in formula:
        # clauses involving this var with same value, fully excluded
        if (var, value) in clause:
            continue
        # clauses involving this var but opposite value, just remove that literal
        new_clause = [literal for literal in clause if literal != (var, not value)]
        new_formula.append(new_clause)
    return new_formula


def has_empty_clause(formula):
    """
    Check if the formula contains an empty clause.

    >>> has_empty_clause([ [('a', True)], [] ])
    True
    >>> has_empty_clause([ [('a', True)], [('b', False)] ])
    False
    """
    for clause in formula:
        if clause == []:
            return True
    return False


def simplify_unit_clauses(formula):
    """
    Simplify the formula by repeatedly applying unit clause elimination.

    formula: a CNF formula

    Returns: a tuple (new_formula, result) where new_formula is the
        simplified formula and result is a dictionary of variable
        assignments made during simplification. Does not mutate input formula.

    >>> simplify_unit_clauses([[('a', True)], [('b', False), ('a', False)]])
    ([], {'a': True, 'b': False})
    >>> simplify_unit_clauses([[('a', True), ('b', False)], [('c', True)]])
    ([[('a', True), ('b', False)]], {'c': True})
    """
    result = {}
    new_formula = []
    for clause in formula:
        new_formula.append(clause[:])
    # Great way to keep doing something until you can't anymore:
    # use a while True loop, make list of stuff you need to act on,
    # break out of loop once there is no more of this stuff,
    # otherwise do your actions, update accordingly, then check again
    while True:
        unit_clauses = [clause for clause in new_formula if len(clause) == 1]
        if not unit_clauses:
            break
        for clause in unit_clauses:
            var, value = clause[0]
            result[var] = value
            new_formula = update_formula(new_formula, var, value)
            # Double check if we have base case after doing all this:
            if new_formula == []:
                return new_formula, result
            if has_empty_clause(new_formula):
                return new_formula, None
    return new_formula, result


def satisfying_assignment(formula):
    """
    Find a satisfying assignment for a given CNF formula.
    Returns that assignment if one exists, or None otherwise. Does not
    mutate input formula.

    >>> satisfying_assignment([])
    {}
    >>> T, F = True, False
    >>> x = satisfying_assignment([[('a', T), ('b', F), ('c', T)]])
    >>> x.get('a', None) is T or x.get('b', None) is F or x.get('c', None) is T
    True
    >>> satisfying_assignment([[('a', T)], [('a', F)]])
    """
    # Base cases:
    # If formula is empty, return empty assignment
    if formula == []:
        return {}
    # If formula contains an empty clause, return None
    if has_empty_clause(formula):
        return None
    # Recursive case:
    # First simplify the problem by assigning things according to unit clauses
    # until no unit clauses left
    simplified = simplify_unit_clauses(formula)
    simplified_formula = simplified[0]
    result = simplified[1]
    # Double check if we have base case after doing all this:
    if simplified_formula == []:
        return result
    if result is None:
        return None
    # Now we go through rest of stuff
    first_clause = simplified_formula[0]
    for var, value in first_clause:
        new_result = satisfying_assignment(
            update_formula(simplified_formula, var, value)
        )
        if new_result is not None:
            result.update(new_result)
            result[var] = value
            return result
    return None
    # todo: check if empty more frequenctly


def combinations(lst, n):
    """
    Generate all combinations of n elements from the input list.

    list: a list of elements
    n: a positive integer

    Returns: a list of lists, where each inner list is a combination of n
        elements from the input list. The order of combinations and the order
        of elements within each combination does not matter.

    >>> combinations(['a', 'b', 'c'], 2)
    [['a', 'b'], ['a', 'c'], ['b', 'c']]
    >>> combinations([1, 2, 3, 4], 3)
    [[1, 2, 3], [1, 2, 4], [1, 3, 4], [2, 3, 4]]
    """
    if n == 0:
        return [[]]
    if len(lst) < n:
        return []
    result = []
    # what is first element of list
    for i in range(len(lst)):
        elem = lst[i]
        rest_combos = combinations(lst[i + 1 :], n - 1)
        for combo in rest_combos:
            result.append([elem] + combo)
    return result


def boolify_scheduling_problem(student_preferences, room_capacities):
    """
    Convert a quiz-room-scheduling problem into a Boolean formula.

    student_preferences: a dictionary mapping a student name (string) to a set
                         of room names (strings) that work for that student

    room_capacities: a dictionary mapping each room name to a positive integer
                     for how many students can fit in that room

    Returns: a CNF formula encoding the scheduling problem which can serve as
        an input to satisfying_assignment, as per the lab write-up

    We assume no student or room names contain underscores. This function
    should not mutate its inputs.
    """
    # First make list of all the vars
    all_vars = []
    for student in student_preferences:
        for room in room_capacities:
            all_vars.append((student + "_" + room))

    formula = []

    # Each student in exactly one room
    # => For all combos of 2 rooms for each student,
    #    student not in both rooms
    for student in student_preferences:
        rooms = list(student_preferences[student])
        for i in range(len(rooms)):
            for j in range(i + 1, len(rooms)):
                room1 = rooms[i]
                room2 = rooms[j]
                formula.append(
                    [(student + "_" + room1, False), (student + "_" + room2, False)]
                )
        # Student in at least one room they like
        clause = []
        for room in student_preferences[student]:
            clause.append((student + "_" + room, True))
        formula.append(clause)
    # Room Capacities
    # if a given room can contain N students,
    # then in every possible group of n+1 students,
    # there must be at least one student who is not in the given room.
    for room in room_capacities:
        capacity = room_capacities[room]
        students = list(student_preferences.keys())
        student_combos = combinations(students, capacity + 1)
        for combo in student_combos:
            clause = []
            for student in combo:
                clause.append((student + "_" + room, False))
            formula.append(clause)

    return formula


if __name__ == "__main__":
    _doctest_flags = doctest.NORMALIZE_WHITESPACE | doctest.ELLIPSIS
    doctest.testmod(optionflags=_doctest_flags)

    # cnf = [[('b', True)]]
    # print(satisfying_assignment(cnf))
    # print(simplify_unit_clauses(cnf))
