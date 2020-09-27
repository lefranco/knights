#!/usr/bin/env python3

"""
File : cavaliers

A knight touches all black cases in grid
Relies on module intersect captured from the net to determine intersections between segments
NOT compatible with pypy because of PIL and windows specificties

"""

import argparse
import csv
import typing
import itertools
import math
import heapq
import copy
import collections
import sys
import time

# profiling
import cProfile
import pstats

if sys.platform == 'win32':
    # windows (detect key pressed)
    import msvcrt
    # windows (make sound)
    import winsound

import PIL.Image
import PIL.ImageDraw
import PIL.ImageFont
import PIL.ImageOps

import intersect

# Set this to true to profile functions (but program will be slow)
PROFILE = False

# set to true to have better insight (but program will be slow)
DEBUG = False

FONT_SMALLER = PIL.ImageFont.truetype("Hack-Regular.ttf", 10)
FONT_NORMAL = PIL.ImageFont.truetype("Hack-Regular.ttf", 12)
FONT_BIGGER = PIL.ImageFont.truetype("Hack-Regular.ttf", 20)

# how many other step points do we link to a step point ?
NB_CLOSEST_TO_LINK = 5

# this is the number of best paths we keep for a couple of step points we consider joining
NB_PATHS_MIN_SELECTED = 7

# we do not accept paths more expensive than this
WORST_PATH_COST = 9

# do we continue after finding a solution ?
CONTINUE_AFTER = False

# we stop if we cannot reach this
TARGET: typing.Optional[int] = None


def distance(point1: typing.Tuple[float, float], point2: typing.Tuple[float, float]) -> float:
    """ This is the euclidian usual distance """
    return math.sqrt((point2[0] - point1[0])**2 + (point2[1] - point1[1])**2)


class Name:
    """ Gives a name to step points """

    _counter = 0

    def __init__(self) -> None:
        limit = ord('Z') - ord('A') + 1
        if Name._counter < limit:
            self._value = chr(ord('A') + Name._counter)
        else:
            assert Name._counter < limit ** 2, "Too many step points"
            self._value = chr(ord('A') + Name._counter // limit) + chr(ord('A') + Name._counter % limit)
        Name._counter += 1

    @property
    def value(self) -> str:
        """ property """
        return self._value


class GenericCell:
    """ A generic cell """

    def __init__(self, row: int, col: int) -> None:
        self._col = col
        self._row = row
        self._moves: typing.List[Move] = list()

    def add_move(self, move: 'Move') -> None:
        """ ads a move to the cell (a knight on the cell) """
        self._moves.append(move)

    @property
    def row(self) -> int:
        """ property """
        return self._row

    @property
    def col(self) -> int:
        """ property """
        return self._col

    @property
    def moves(self) -> typing.List['Move']:
        """ property """
        return self._moves

    def __hash__(self) -> int:
        # most time spent in here
        return hash((self._row, self._col))

    def __eq__(self, other: 'GenericCell') -> bool:  # type: ignore
        return (other.row, other.col) == (self._row, self._col)

    def __lt__(self, other: 'GenericCell') -> bool:
        return (self._row, self._col) < (other.row, other.col)


class StandardCell(GenericCell):
    """ A cell but not step point """

    def __init__(self, row: int, col: int, value: int) -> None:
        GenericCell.__init__(self, row, col)
        self._value = value

    @property
    def value(self) -> int:
        """ property """
        return self._value

    def __str__(self) -> str:
        return f"(r{self.row} c{self.col})"


class StepPoint(GenericCell):
    """ A step point cell (black without value) """

    def __init__(self, row: int, col: int) -> None:
        GenericCell.__init__(self, row, col)
        self._name = Name()

    @property
    def name(self) -> Name:
        """ property """
        return self._name

    def __str__(self) -> str:
        return self.name.value


class Pair:
    """ A pair : two cells, order does not matter """

    def __init__(self, start: GenericCell, dest: GenericCell) -> None:
        assert start != dest
        if start < dest:
            self._start = start
            self._dest = dest
        else:
            self._start = dest
            self._dest = start

    def other(self, cell: GenericCell) -> GenericCell:
        """ the other one of the move """
        if cell is self._start:
            return self._dest
        if cell is self._dest:
            return self._start
        assert False
        return self._start

    def content(self) -> typing.Tuple[GenericCell, GenericCell]:
        """ content """
        return self._start, self._dest

    def __hash__(self) -> int:
        return hash(self.content())

    def __eq__(self, other: 'Pair') -> bool:  # type: ignore
        return other.content() == self.content()

    def __lt__(self, other: 'Pair') -> bool:
        # arbitrary
        return self.content() < other.content()

    def __contains__(self, cell: StepPoint) -> bool:
        return cell is self._start or cell is self._dest

    def __str__(self) -> str:
        return f"{self._start}-{self._dest}"


class Move:
    """ A move (based on a pair) """

    def __init__(self, grid: 'Grid', start: GenericCell, dest: GenericCell) -> None:
        self._grid = grid
        self._pair = Pair(start, dest)
        self._middle = ((start.row + dest.row) / 2, (start.col + dest.col) / 2)

    def conflicts(self, other: 'Move') -> bool:
        """ Says if two moves conflict """
        # MOST EXPENSIVE FUNCTION FROM PROFILING """

        # a move conflicts with itself
        if other == self:
            return True

        # do not confict if touch from an end
        # line below removed after profiling
        # assert set(other.pair.content()) != set(self._pair.content()), "Pb conclicts"

        if set(other.pair.content()) & set(self._pair.content()):
            return False

        # eventually check if segments intersect
        possible_conflict = frozenset([self, other])
        return possible_conflict in self._grid.conflicting_moves

    @property
    def pair(self) -> Pair:
        """ property """
        return self._pair

    @property
    def middle(self) -> typing.Tuple[float, float]:
        """ property """
        return self._middle

    def __hash__(self) -> int:
        return hash(self._pair)

    def __eq__(self, other: 'Move') -> bool:  # type: ignore
        return other.pair == self._pair

    def __lt__(self, other: 'Move') -> bool:
        return self._pair < other.pair

    def __str__(self) -> str:
        return f"{str(self._pair)}"


class Path:
    """ A path (a list of moves) """

    def __init__(self, grid: 'Grid') -> None:
        self._grid = grid
        self._pair: typing.Optional[Pair] = None
        self._insiders: typing.Set[StandardCell] = set()
        self._content: typing.List[Move] = list()
        self._cost: typing.Optional[int] = None
        self._rank: typing.Optional[int] = None

    def insert(self, move: Move) -> None:
        """ insert """

        # add the move
        self._content.append(move)

        # I was empty, I copy the pair
        if self._pair is None:
            self._pair = move.pair
            return

        # otherwise merge my pair with incomping move
        joining_cell_set = set(self._pair.content()) & set(move.pair.content())
        assert joining_cell_set, "pb insert in path 1"
        assert len(joining_cell_set) == 1, "pb insert in path 2"
        joining_cell = list(joining_cell_set)[0]

        new_cell = move.pair.other(joining_cell)
        old_cell = self._pair.other(joining_cell)
        self._pair = Pair(old_cell, new_cell)
        self._insiders.add(typing.cast(StandardCell, joining_cell))

    def conflicts(self, other: 'Path') -> bool:
        """ Says if two paths conflit """

        # must have distinct insiders
        if self._insiders & other.insiders:
            return True

        # must not have intersecting moves
        for move1 in self._content:
            for move2 in other.content:
                if move1.conflicts(move2):
                    return True

        return False

    @property
    def pair(self) -> typing.Optional[Pair]:
        """ property """
        return self._pair

    @pair.setter
    def pair(self, pair: Pair) -> None:
        """ --- """
        self._pair = pair

    @property
    def content(self) -> typing.List[Move]:
        """ property """
        return self._content

    @content.setter
    def content(self, content: typing.List[Move]) -> None:
        """ --- """
        self._content = content

    @property
    def insiders(self) -> typing.Set[StandardCell]:
        """ property """
        return self._insiders

    @insiders.setter
    def insiders(self, insiders: typing.Set[StandardCell]) -> None:
        """ --- """
        self._insiders = insiders

    @property
    def cost(self) -> typing.Optional[int]:
        """ property """
        return self._cost

    @cost.setter
    def cost(self, cost: int) -> None:
        """ --- """
        self._cost = cost

    @property
    def rank(self) -> typing.Optional[int]:
        """ property """
        return self._rank

    @rank.setter
    def rank(self, rank: int) -> None:
        """ --- """
        self._rank = rank

    def __hash__(self) -> int:
        return hash(" ".join([str(m) for m in self._content]))

    def __eq__(self, other: 'Path') -> bool:  # type: ignore
        if other.pair != self._pair:
            return False
        return set(other.content) == set(self._content)

    def __lt__(self, other: 'Path') -> bool:
        assert self._pair is not None
        assert other.pair is not None
        if other.pair != self._pair:
            return self._pair < other.pair
        return self._content < other.content

    def __len__(self) -> int:
        return len(self._content)

    def __copy__(self) -> 'Path':
        mycopy = Path(self._grid)
        mycopy.pair = self._pair
        mycopy.insiders = copy.copy(self._insiders)
        mycopy.content = copy.copy(self._content)
        mycopy.cost = self._cost
        mycopy.rank = self._rank
        return mycopy

    def __str__(self) -> str:
        return f"{self._pair}:" + "<" + "/".join([str(m) for m in self._content]) + ">"


class Network:
    """ Network of cells linked or not """

    def __init__(self, grid: 'Grid', start: StepPoint):
        self._grid = grid
        self._tail = start
        self._head = start
        self._insiders: typing.Set[StepPoint] = set()
        self._content: typing.List[Path] = list()

    def accept(self, path: Path) -> bool:
        """ Do we accept this path in our network ? """

        assert path.pair is not None

        # must join
        if self._head not in set(path.pair.content()):
            return False

        # must not join "inside"
        if set(path.pair.content()) & self._insiders:
            return False

        # must not make a cycle
        if set(path.pair.content()) == set([self._tail, self._head]):
            return False

        # must not conflict (last tested because presumed more costy in cpu)
        for path_here in self._content:
            if path_here.conflicts(path):
                return False

        return True

    def insert(self, path: Path) -> None:
        """ insert path in network """

        assert path.pair is not None
        assert self._head in set(path.pair.content()), "Pb insert : path not joining"
        former_head = self._head
        self._head = typing.cast(StepPoint, path.pair.other(self._head))
        self._insiders.add(former_head)
        self._content.append(path)

    def healthy(self) -> bool:
        """ Decide if this network is healthy """

        def may_connect(step_point1: StepPoint, step_point2: StepPoint) -> bool:
            """ routine """
            pair = Pair(step_point1, step_point2)
            if pair not in self._grid.possible_paths_for_pair:
                return False
            for path in self._grid.possible_paths_for_pair[pair]:
                if path in possible_paths:
                    return True
            return False

        def chain_exists(head: StepPoint, isolated_ones: typing.Set[StepPoint]) -> bool:

            def chain_exists_rec(head: StepPoint, isolated_ones: typing.Set[StepPoint]) -> bool:

                if not isolated_ones:
                    return True

                for cell in isolated_ones:

                    pair = Pair(head, cell)
                    if not may_connect_table[pair]:
                        continue

                    head2 = cell
                    isolated_ones2 = copy.copy(isolated_ones)
                    isolated_ones2 -= set([cell])
                    if chain_exists(head2, isolated_ones2):
                        return True

                return False

            return chain_exists_rec(head, isolated_ones)

        # otherwise never succeed
        if self.complete():
            return True

        # calculate the possible paths
        possible_paths = copy.copy(self._grid.all_possible_paths)
        for path in self._content:
            possible_paths.difference_update(self._grid.conflicts_with[path])

        # calculated the isolated_ones (not in path)
        extremities = set([self._tail, self._head])
        isolated_ones = set(self._grid.step_points)
        isolated_ones.difference_update(extremities)
        isolated_ones.difference_update(self._insiders)

        # calculate the pertinent_ones
        pertinent_ones = isolated_ones | set([self._head])

        # table of possible connections between pertinent ones
        may_connect_table = dict()
        for step_point1, step_point2 in itertools.combinations(pertinent_ones, 2):
            pair = Pair(step_point1, step_point2)
            may_connect_table[pair] = may_connect(step_point1, step_point2)

        # there must be a chain starting from head and covering everyone
        return chain_exists(self._head, isolated_ones)

    def empty(self) -> bool:
        """ if empty """
        return len(self._content) == 0

    def complete(self) -> bool:
        """ Decide if everyone connected """
        return len(self._content) == len(self._grid.step_points) - 1

    def all_paths(self) -> typing.List[Path]:
        """ paths list  """
        return self._content

    def nb_paths(self) -> int:
        """ how many paths ? """
        return len(self._content)

    def cost(self) -> int:
        """ cost ? """
        return sum([p.cost if p.cost is not None else 0 for p in self._content])

    @property
    def tail(self) -> StepPoint:
        """ property """
        return self._tail

    @tail.setter
    def tail(self, tail: StepPoint) -> None:
        """ --- """
        self._tail = tail

    @property
    def head(self) -> StepPoint:
        """ property """
        return self._head

    @head.setter
    def head(self, head: StepPoint) -> None:
        """ --- """
        self._head = head

    @property
    def insiders(self) -> typing.Set[StepPoint]:
        """ property """
        return self._insiders

    @insiders.setter
    def insiders(self, insiders: typing.Set[StepPoint]) -> None:
        """ --- """
        self._insiders = insiders

    @property
    def content(self) -> typing.List[Path]:
        """ property """
        return self._content

    @content.setter
    def content(self, content: typing.List[Path]) -> None:
        """ --- """
        self._content = content

    def __copy__(self) -> 'Network':
        start = self._tail
        mycopy = Network(self._grid, start)
        mycopy.head = self._head
        mycopy.insiders = copy.copy(self._insiders)
        mycopy.content = copy.copy(self._content)
        return mycopy

    def __str__(self) -> str:
        return "\n".join([str(p) for p in self._content])


class Grid:
    """ Grid """
    def __init__(self, file_name: str) -> None:

        def could_jump(start: GenericCell, dest: GenericCell) -> bool:
            return set([abs(dest.row - start.row), abs(dest.col - start.col)]) == set([1, 2])

        def does_conflict(move1: Move, move2: Move) -> bool:
            """ two moves conflict if the segments have intersection """

            # eliminate if too far ways (optimisation)
            if distance(move1.middle, move2.middle) > math.sqrt(5) + 0.01:
                return False

            # determine segments
            start1, dest1 = move1.pair.content()
            start2, dest2 = move2.pair.content()
            point_s1 = intersect.Point(start1.row, start1.col)  # type: ignore
            point_d1 = intersect.Point(dest1.row, dest1.col)  # type: ignore
            point_s2 = intersect.Point(start2.row, start2.col)  # type: ignore
            point_d2 = intersect.Point(dest2.row, dest2.col)  # type: ignore

            # use algo from geeksforgeeks
            return intersect.doIntersect(point_s1, point_d1, point_s2, point_d2)  # type: ignore

        self._step_points: typing.List[StepPoint] = list()
        self._cells: typing.List[GenericCell] = list()
        self._table: typing.Dict[typing.Tuple[int, int], GenericCell] = dict()
        self._nb_cols = 0

        # from file build cells
        print("loading grid")
        with open(file_name, newline='') as csv_file:
            csv_reader = csv.reader(csv_file, delimiter=';')
            self._nb_rows = 0
            for row_num, row_content in enumerate(csv_reader):
                nb_cols = len(row_content)
                if self._nb_cols == 0:
                    self._nb_cols = nb_cols
                else:
                    assert nb_cols == self._nb_cols
                for col_num, col_content in enumerate(row_content):
                    if col_content == 'x':
                        step_point = StepPoint(row_num, col_num)
                        self._step_points.append(step_point)
                        self._table[(row_num, col_num)] = step_point
                        self._cells.append(step_point)
                    else:
                        value = int(col_content)
                        standard_cell = StandardCell(row_num, col_num, value)
                        self._table[(row_num, col_num)] = standard_cell
                        self._cells.append(standard_cell)
                self._nb_rows += 1
        print(f"grid has {len(self._cells)} cells")
        print(f"grid has {len(self._step_points)} step points (black cells)")

        # from cells build moves
        print("determining moves...")
        self._moves: typing.List[Move] = list()
        for start, dest in itertools.combinations(self._cells, 2):
            if could_jump(start, dest):
                move = Move(self, start, dest)
                self._moves.append(move)
        print(f"grid has {len(self._moves)} moves")

        # determinine conflicting moves
        self._conflicting_moves: typing.Set[typing.FrozenSet[Move]] = set()
        print("determining conflicting moves...")
        for move1, move2 in itertools.combinations(self._moves, 2):
            if does_conflict(move1, move2):
                conflict = frozenset([move1, move2])
                self._conflicting_moves.add(conflict)
        print(f"grid has {len(self._conflicting_moves)} (potentially) conflicting moves")

        # every cell gets its moves
        print("adding moves to cells")
        for move in self._moves:
            start, dest = move.pair.content()
            start.add_move(move)
            dest.add_move(move)
        print("moves added")

        # to be calculated later
        self._possible_paths_for_pair: typing.Dict[Pair, typing.List[Path]] = dict()
        self._all_possible_paths: typing.Set[Path] = set()
        self._possible_paths_for_step_point: typing.Dict[StepPoint, typing.Set[Path]] = collections.defaultdict(set)
        self._conflicts_with: typing.Dict[Path, typing.Set[Path]] = collections.defaultdict(set)

    def extract_paths(self, start: StepPoint, dest: StepPoint, number_limit: int, cost_limit: int) -> typing.List[Path]:
        """ all paths from point start to point dest """

        found_paths: typing.List[Path] = list()
        nb_paths_found = 0
        cur_rank_path = 0
        prev_cost: typing.Optional[int] = None

        # on heap : cost so far / cell / list of moves
        todo: typing.List[GenericCell] = list()
        cost = 0
        dist = distance((start.col, start.row), (dest.col, dest.row))

        # heap has :
        #  - cost of path (first criterion to be as low as possible)
        #  - distance to dest (second criterion to be as low as possible)
        #  - cell it self
        #  - path (= list of moves, moves = pair of cells)
        heapq.heappush(todo, (cost, dist, start, Path(self)))  # type: ignore

        while todo:

            # extract next cell
            studied_cell: GenericCell
            path_so_far: Path
            cost, dist, studied_cell, path_so_far = heapq.heappop(todo)  # type: ignore

            # get all possibilities from it
            reachables = [(m.pair.other(studied_cell), m) for m in studied_cell.moves]

            for reachable, move in reachables:

                # conflicts with rest of path : ignore
                conflicting = False
                for prev_move in path_so_far.content:
                    if prev_move.conflicts(move):
                        conflicting = True
                        break
                if conflicting:
                    continue

                # cannot come back to start
                if reachable == start:
                    continue

                # cannot cross itself
                if reachable in path_so_far.insiders:
                    continue

                # dest : we have a path
                new_path = copy.copy(path_so_far)
                new_path.insert(move)
                if isinstance(reachable, StandardCell):
                    new_cost = cost + reachable.value
                new_path.cost = cost

                if reachable is dest:
                    nb_paths_found += 1
                    print('+', end='', flush=True)
                    if prev_cost is None or new_path.cost > prev_cost:
                        if nb_paths_found > number_limit or new_path.cost > cost_limit:
                            print()
                            return found_paths
                        cur_rank_path = nb_paths_found
                    new_path.rank = cur_rank_path
                    prev_cost = new_path.cost
                    found_paths.append(new_path)
                    continue

                # black : ignore
                if isinstance(reachable, StepPoint):
                    continue

                # continue from there
                new_dist = distance((reachable.col, reachable.row), (dest.col, dest.row))
                heapq.heappush(todo, (new_cost, new_dist, reachable, new_path))  # type: ignore

        return found_paths

    def calc_best_paths(self, impeached_pairs: typing.List[Pair]) -> None:
        """ Calculate best paths for couples of step points """

        # Decide which paths we build
        links: typing.Set[Pair] = set()
        for step_point in self._step_points:
            other_ones = [s for s in self._step_points if s != step_point]
            closest_ones = sorted(other_ones, key=lambda s, sp=step_point: distance((sp.col, sp.row), (s.col, s.row)))  # type:ignore
            for other in closest_ones[:NB_CLOSEST_TO_LINK]:
                pair = Pair(step_point, other)
                links.add(pair)

        # removed impeached pair
        for impeached_pair in impeached_pairs:
            links.remove(impeached_pair)

        print("Calculating best paths between selected pairs...")
        for num_pair, pair in enumerate(links):

            step1, step2 = pair.content()
            assert isinstance(step1, StepPoint)
            assert isinstance(step2, StepPoint)
            print(f"Searching at least {NB_PATHS_MIN_SELECTED} best path(s) costing at most {WORST_PATH_COST} between {step1} and {step2} ({num_pair+1}/{len(links)})...")
            path_list = self.extract_paths(step1, step2, NB_PATHS_MIN_SELECTED, WORST_PATH_COST)
            if not path_list:
                print("*** No possible path.")
            else:
                self._possible_paths_for_pair[pair] = path_list

                # in a file for debug
                if DEBUG:
                    for num_path, path in enumerate(self._possible_paths_for_pair[pair]):
                        first_name = min(step1.name.value, step2.name.value)
                        second_name = max(step1.name.value, step2.name.value)
                        file_name = f"Riders_path_{first_name}_{second_name}_{num_path}.png"
                        picture = Picture(self, file_name, True)
                        picture.put_path(path)
                        legend = f"Cost = {path.cost} moves={len(path.content)}"
                        picture.put_legend(legend)
                        picture.output()

        # calculate two other lists of possible paths
        for pair, paths in self._possible_paths_for_pair.items():
            self._all_possible_paths.update(paths)
            step1, step2 = pair.content()
            assert isinstance(step1, StepPoint)
            assert isinstance(step2, StepPoint)
            self._possible_paths_for_step_point[step1].update(paths)
            self._possible_paths_for_step_point[step2].update(paths)

    def stats_paths(self, circuit: 'Circuit') -> None:
        """ stats about paths """

        cost_cheapest_path: typing.Dict[Pair, int] = dict()
        cost_most_expensive_path: typing.Dict[Pair, int] = dict()
        for pair, paths in self._possible_paths_for_pair.items():
            cheapest_path = min(paths, key=lambda p: p.cost)
            most_expensive_path = max(paths, key=lambda p: p.cost)
            assert cheapest_path.cost is not None
            assert most_expensive_path.cost is not None
            cost_cheapest_path[pair] = cheapest_path.cost
            cost_most_expensive_path[pair] = most_expensive_path.cost
        sorted_pairs = sorted(self._possible_paths_for_pair, key=lambda p: cost_cheapest_path[p])

        nb_hits = 0
        for pair in sorted_pairs:
            print(f"Pair {pair} : ", end='')
            print(f"I have {len(self._possible_paths_for_pair[pair])} paths ", end='')
            min_cost = cost_cheapest_path[pair]
            print(f"Shortest path costs {cost_cheapest_path[pair]} ", end='')
            print(f"Most expensive costs {cost_most_expensive_path[pair]} ", end='')
            path_pairs = set(self._possible_paths_for_pair[pair]) & set(circuit.paths)
            if path_pairs:
                assert len(path_pairs) == 1
                path_pair = path_pairs.pop()
                path_cost = path_pair.cost
                print(f"Taken path costs {path_pair.cost} ", end='')
                if path_cost == min_cost:
                    nb_hits += 1
                    print("optimal ", end='')
            print()
        print(f"Number optimal choices = {nb_hits} / {len(circuit.paths)}")

        # for what it is worth
        nb_paths = len(self._step_points) - 1
        theoretical_limit = sum([cost_cheapest_path[p] for p in sorted_pairs[:nb_paths]])
        print(f"Pretty much convinced cannot go beyond circuit cost {theoretical_limit}")

        print("Best paths calculated.")

    def calc_conflict_paths(self) -> None:
        """ conflicting paths """

        time_unit = 10000
        nb_poss_paths = len(self._all_possible_paths)
        crosses = nb_poss_paths * (nb_poss_paths - 1) // 2 // time_unit
        print(f"Conflict table (nb paths = {nb_poss_paths} expect {crosses} '+')...")

        # calculate conflict table
        num = 0
        for path1, path2 in itertools.combinations(self._all_possible_paths, 2):
            if path1.conflicts(path2):
                self._conflicts_with[path1].add(path2)
                self._conflicts_with[path2].add(path1)
            num += 1
            if num % time_unit == 0:
                print('+', end='', flush=True)
        print()

    def calc_starting_step_point(self) -> StepPoint:
        """ best starting point """

        print(f"Calculating best starting point...")

        cost_best_path_reaching = dict()
        for step_point in self._step_points:
            best_path = min(self._possible_paths_for_step_point[step_point], key=lambda p: p.cost)
            cost_best_path_reaching[step_point] = best_path.cost
        sorted_step_points = sorted(cost_best_path_reaching, key=lambda s: (cost_best_path_reaching[s], -len(self._possible_paths_for_step_point[s]), s), reverse=True)
        for step_point in sorted_step_points:
            best_cost = cost_best_path_reaching[step_point]
            nb_paths = len(self._possible_paths_for_step_point[step_point])
            print(f"Starting candidate {step_point} for best_cost(+)={best_cost} nb_paths(-)={nb_paths}")

        chosen_step_point = sorted_step_points[0]
        print(f"Will start from {chosen_step_point}")
        return chosen_step_point

    def calc_complete_circuit(self, start_step: StepPoint, forced_start_pairs: typing.List[Pair], encouraged_pairs: typing.Set[Pair], target: typing.Optional[int]) -> typing.Optional['Circuit']:
        """ Calculate a complete circuit (aim of all that !) """

        # must be defined here since accessed in sub functions
        number = 1
        best_so_far = 0
        best_score_so_far: typing.Optional[Score] = None
        num_sol = 1

        def heuristic(path: Path, start: bool, now_conflicts: typing.Dict[Path, typing.Set[Path]], now_accesses: typing.Dict[StepPoint, int]) -> typing.Tuple[bool, int, int, int, int, int, typing.List[typing.Tuple[int, int]]]:
            """ Which paths do we prefer ? """

            # In order to be as deterministic as possible, there must be many criterions
            # 1 we prefer encouraged path
            # 2 we prefer cheaper paths
            # 3 we prefer paths that reach step points with little access
            # 4 we prefer less conclicting paths
            # 5 we prefer shortest paths
            # 6 we prefer paths with smallest value of cell inside as big as possible (leaving zeroes to other paths)
            # 7 we prefer according to coords of cells of path

            # The higher the heuristic, the better
            assert path.cost is not None
            assert path.pair is not None
            step1, step2 = path.pair.content()
            assert isinstance(step1, StepPoint)
            assert isinstance(step2, StepPoint)
            encouraged = not start and path.pair in encouraged_pairs
            return encouraged, -path.cost, -min(now_accesses[step1], now_accesses[step2]), -len(now_conflicts[path]), -len(path.content), -min([c.value for c in path.insiders]), [(c.row, c.col) for c in path.insiders]

        def calc_complete_circuit_rec(possible_paths: typing.Set[Path], network: Network) -> typing.Optional[Circuit]:

            print(f"Possible paths={len(possible_paths)} inserted paths={network.nb_paths()} cost={network.cost()}")

            nb_paths = network.nb_paths()

            # we trace best so far positions
            nonlocal best_so_far
            if nb_paths > best_so_far:
                circuit = Circuit(self, network, "best intermediate")
                circuit.show(f"Riders_attempt_{nb_paths}.png", True)
                best_so_far = nb_paths

            # are we done ?
            if network.complete():
                circuit = Circuit(self, network, "final")
                circuit.optimize()
                if not CONTINUE_AFTER:
                    return circuit
                score = circuit.score()
                nonlocal best_score_so_far
                if best_score_so_far is None or score < best_score_so_far:
                    winsound.Beep(2500, 1000)
                    print(f"==== Storing a solution with {score} =====")
                    nonlocal num_sol
                    circuit.show(f"Riders_sol_{num_sol}_sc_{score.cost}_{score.size}.png", True)   # with debug info
                    circuit.show(f"Riders_{score.cost}_{score.size}.png", False)  # for delivery
                    num_sol += 1
                    best_score_so_far = score

            # we trace  intermediate positions when keyboard hit
            if sys.platform == 'win32':
                # windows
                if msvcrt.kbhit():  # type: ignore
                    _ = msvcrt.getch()  # type: ignore
                    circuit = Circuit(self, network, "all intermediate")
                    nonlocal number
                    circuit.show(f"Riders_attempt_{nb_paths:03}_{number:03}.png", True)
                    number += 1

            # there is a target score : give up if reached (was not a solution)
            if target is not None and not network.complete() and network.cost() > target:
                return None

            # when starting : special : encourage does not apply
            start = network.empty()

            # update the conflict table
            now_conflicts = {p: (self._conflicts_with[p] & possible_paths) for p in possible_paths}

            # update the access table
            now_accesses = {s: len([p for p in possible_paths if p.pair is not None and s in set(p.pair.content())]) for s in self._step_points}

            # what can we do from here ?
            sorted_paths = sorted(possible_paths, key=lambda p: heuristic(p, start, now_conflicts, now_accesses), reverse=True)

            for path in sorted_paths:

                if not network.accept(path):
                    continue

                # make a bigger network
                network2 = copy.copy(network)
                network2.insert(path)

                # check it makes sense
                if not network2.healthy():
                    continue

                # shrink the path list to choose from
                possible_paths2 = copy.copy(possible_paths)

                # remove paths with this pair
                assert path.pair is not None
                way = path.pair
                paths_removed = self._possible_paths_for_pair[way]
                possible_paths2.difference_update(paths_removed)

                # remove paths conflicting with this one
                paths_conflicting = now_conflicts[path]
                possible_paths2.difference_update(paths_conflicting)

                # and now recurse...
                found_circuit = calc_complete_circuit_rec(possible_paths2, network2)
                if found_circuit is not None:
                    return found_circuit

            return None

        print(f"Calculating a complete circuit starting from {start_step}...")

        # we shall work on a copy
        possible_paths = set(self._all_possible_paths)
        network = Network(self, start_step)

        for num_pair, forced_pair in enumerate(forced_start_pairs):

            assert forced_pair in self._possible_paths_for_pair, f"I did not calculate paths between {forced_pair}"
            paths_pair = self._possible_paths_for_pair[forced_pair]

            good_path: typing.Optional[Path] = None
            for path in paths_pair:

                if not network.accept(path):
                    continue

                network.insert(path)
                if not network.healthy():
                    continue

                good_path = path
                break

            else:
                assert False, f"Could not insert a path between {forced_pair}"

            # remove path with same pair
            possible_paths.difference_update(paths_pair)

            # remove paths conflicting with this one
            paths_conflicting = self._conflicts_with[good_path]
            possible_paths.difference_update(paths_conflicting)

            circuit = Circuit(self, network, "forced ")
            circuit.show(f"Riders_forced_{num_pair + 1}.png", True)

        return calc_complete_circuit_rec(possible_paths, network)

    def step_point_from_name(self, name: str) -> typing.Optional[StepPoint]:
        """ step_from_name """
        for step_point in self._step_points:
            if step_point.name.value == name:
                return step_point

        return None

    @property
    def nb_cols(self) -> int:
        """ property """
        return self._nb_cols

    @property
    def nb_rows(self) -> int:
        """ property """
        return self._nb_rows

    @property
    def table(self) -> typing.Dict[typing.Tuple[int, int], GenericCell]:
        """ property """
        return self._table

    @property
    def step_points(self) -> typing.List[StepPoint]:
        """ property """
        return self._step_points

    @property
    def conflicting_moves(self) -> typing.Set[typing.FrozenSet[Move]]:
        """ property """
        return self._conflicting_moves

    @property
    def possible_paths_for_step_point(self) -> typing.Dict[StepPoint, typing.Set[Path]]:
        """ property """
        return self._possible_paths_for_step_point

    @property
    def possible_paths_for_pair(self) -> typing.Dict[Pair, typing.List[Path]]:
        """ property """
        return self._possible_paths_for_pair

    @property
    def conflicts_with(self) -> typing.Dict[Path, typing.Set[Path]]:
        """ property """
        return self._conflicts_with

    @property
    def all_possible_paths(self) -> typing.Set[Path]:
        """ property """
        return self._all_possible_paths

    def __str__(self) -> str:
        text = ""
        text += f"{self._nb_rows} rows {self._nb_cols} cols"
        text += "\n"
        for row in range(self._nb_rows):
            for col in range(self._nb_cols):
                cell = self._table[(row, col)]
                if isinstance(cell, StepPoint):
                    text += 'x'
                if isinstance(cell, StandardCell):
                    text += str(cell.value)
                text += " "
            text += "\n"
        return text


class Score:
    """ Actual score """

    def __init__(self, cost: int, size: int) -> None:
        self._cost = cost
        self._size = size

    @property
    def cost(self) -> int:
        """ property """
        return self._cost

    @property
    def size(self) -> int:
        """ property """
        return self._size

    def __eq__(self, other: 'Score') -> bool:  # type: ignore
        return (other.cost, other.size) == (self._cost, self._size)

    def __lt__(self, other: 'Score') -> bool:
        if self._cost != other.cost:
            return self._cost < other.cost
        return self._size > other.size

    def __sub__(self, other: 'Score') -> 'Score':
        return Score(self._cost - other.cost, self._size - other.size)

    def __str__(self) -> str:
        return f"[cost(-)={self._cost} size(+)={self._size}]"


def score_path(path: typing.Optional[Path]) -> Score:
    """ Score of a path (even if score should apply to circuits only actually """

    cost = 0
    size = 0
    if path is not None:
        cost = path.cost if path.cost is not None else 0
        size = len(path.content)
    return Score(cost, size)


class Circuit:
    """ A circuit """

    def __init__(self, grid: Grid, network: Network, info: str) -> None:
        self._grid = grid
        self._info = info
        self._paths = network.content

    def score(self) -> Score:
        """ score """
        cost = sum([p.cost for p in self._paths if p.cost is not None])
        size = sum([len(p.content) for p in self._paths])
        return Score(cost, size)

    @property
    def paths(self) -> typing.List[Path]:
        """ property """
        return self._paths

    def optimize(self) -> None:
        """ we re happy to have it, let's see if we can still improve it ! """

        print("Optimizing...")

        while True:

            if DEBUG:
                print(f"We have a circuit with score {self.score()}")

            # see who can replace any path
            candidates_replacement: typing.Dict[Path, typing.Set[Path]] = dict()
            for installed_path in self._paths:
                pair = installed_path.pair
                assert pair is not None
                candidates_replacement[installed_path] = set(self._grid.possible_paths_for_pair[pair])
                candidates_replacement[installed_path].remove(installed_path)

            # remove conflicting ones
            for installed_path1, installed_path2 in itertools.combinations(self._paths, 2):
                candidates_replacement[installed_path1] -= self._grid.conflicts_with[installed_path2]
                candidates_replacement[installed_path2] -= self._grid.conflicts_with[installed_path1]

            if DEBUG:
                print("Replacers :")
                for path in self._paths:
                    print(f"path {path} has {len(candidates_replacement[path])} replacers")

            # find the best per path
            best_replacer: typing.Dict[Path, Path] = dict()
            best_replacer_gain: typing.Dict[Path, Score] = dict()
            for installed_path in self._paths:
                if not candidates_replacement[installed_path]:
                    continue
                best_possible_replacer = min(candidates_replacement[installed_path], key=score_path)
                gain = score_path(installed_path) - score_path(best_possible_replacer)
                if DEBUG:
                    print(f"replacing {installed_path} by {best_possible_replacer} would gain {score_path(installed_path)} - {score_path(best_possible_replacer)} = {gain}")
                if gain > score_path(None):
                    best_replacer[installed_path] = best_possible_replacer
                    best_replacer_gain[installed_path] = gain

            # find the best overall
            if not best_replacer_gain:
                # print(f"Mmm. Cannot do better it seems...")
                break
            victim_path = min(best_replacer, key=lambda r: best_replacer_gain[r])
            gain = best_replacer_gain[victim_path]

            if DEBUG:
                print(f"We replace victim path is {victim_path} for gain {gain}")

            # now do the replacement
            index_victim = self._paths.index(victim_path)
            self._paths[index_victim] = best_replacer[victim_path]

    def show(self, file_name: str, debug: bool) -> None:
        """ show in file """

        # in a file for debug
        picture = Picture(self._grid, file_name, debug)
        sum_costs = 0
        sum_moves = 0
        for path in self._paths:
            picture.put_path(path)
            assert path.cost is not None
            sum_costs += path.cost
            sum_moves += len(path)
        legend = f"Cost = {sum_costs} moves={sum_moves} paths={len(self._paths)}"
        if debug:
            picture.put_explanation("Paths : cost/rank for cost/size")
        picture.put_legend(legend)
        picture.put_info(self._info)
        picture.output()

    def __str__(self) -> str:
        return " ".join([str(p) for p in self._paths])


class Picture:
    """ A picture that will go in a png file"""

    def __init__(self, grid: Grid, filename: str, debug: bool) -> None:

        self._grid = grid
        self._filename = filename
        self._debug = debug

        # create image
        self._image = PIL.Image.new('RGB', (self._grid.nb_cols * 20, (self._grid.nb_rows + 4) * 20), color="white")

        # create drawer
        self._draw = PIL.ImageDraw.Draw(self._image)

        # put grid
        for row in range(self._grid.nb_rows):
            for col in range(self._grid.nb_cols):
                cell = self._grid.table[(row, col)]
                if isinstance(cell, StepPoint):
                    self._draw.rectangle(xy=((col * 20 + 5, row * 20 + 5), (col * 20 + 15, row * 20 + 15)), outline="black", fill="white" if debug else "black")
                    if debug:
                        shift = 5 if len(cell.name.value) == 1 else -5
                        self._draw.text(xy=(col * 20 + shift, row * 20), text=cell.name.value, font=FONT_BIGGER, fill="red")
                if isinstance(cell, StandardCell):
                    self._draw.text(xy=(col * 20 + 5, row * 20 + 5), text=str(cell.value), font=FONT_NORMAL, fill="black")

    def put_path(self, path: Path) -> None:
        """ put a path """
        for move in path.content:
            start, dest = move.pair.content()
            self._draw.line((start.col * 20 + 10, start.row * 20 + 10, dest.col * 20 + 10, dest.row * 20 + 10), fill="red")
        assert path.pair is not None
        start, dest = path.pair.content()
        if self._debug:
            col_mid = (start.col + dest.col) / 2.0
            row_mid = (start.row + dest.row) / 2.0
            self._draw.text(xy=(col_mid * 20 + 10, row_mid * 20 + 10), text=f"{path.cost}/{path.rank}/{len(path.content)}", font=FONT_NORMAL, fill="red")

    def put_explanation(self, explanation: str) -> None:
        """ put a legend """
        self._draw.text(xy=(0 * 20 + 5, (self._grid.nb_rows + 1) * 20 + 5), text=explanation, font=FONT_SMALLER, fill="red")

    def put_legend(self, legend: str) -> None:
        """ put a legend """
        self._draw.text(xy=(0 * 20 + 5, (self._grid.nb_rows + 2) * 20 + 5), text=legend, font=FONT_SMALLER, fill="black")

    def put_info(self, info: str) -> None:
        """ put an info """
        self._draw.text(xy=(0 * 20 + 5, (self._grid.nb_rows + 3) * 20 + 5), text=info, font=FONT_SMALLER, fill="grey")

    def output(self) -> None:
        """ output to file """
        self._image.save(self._filename)


def main() -> None:
    """ main """

    parser = argparse.ArgumentParser()
    parser.add_argument('-g', '--grid', required=True, help='file whith grid')
    parser.add_argument('-c', '--closest', required=False, help='closest to link')
    parser.add_argument('-m', '--min_paths', required=False, help='nb paths selected minimum (keep collecting as long as cost is same)')
    parser.add_argument('-w', '--worst_path_cost', required=False, help='worst path cost accepted')
    parser.add_argument('-s', '--search_paths', required=False, nargs=2, help='Search paths between two step points')
    parser.add_argument('-f', '--forced_start', required=False, help='Force to start this step points')
    parser.add_argument('-F', '--forced_start_pairs', required=False, nargs='+', help='Force to start with paths between a list of step points')
    parser.add_argument('-e', '--encouraged_pairs', required=False, nargs='+', help='Encourages a path between list of two step points')
    parser.add_argument('-i', '--impeached_pairs', required=False, nargs='+', help='Impeaches a path between list of two step points')
    parser.add_argument('-C', '--continue_after', required=False, action='store_true', help='continues after finding a solution')
    parser.add_argument('-t', '--target', required=False, help='target score : abort searching branches that lead to higher cost that this')
    args = parser.parse_args()

    file_name = args.grid

    global NB_CLOSEST_TO_LINK
    if args.closest:
        NB_CLOSEST_TO_LINK = int(args.closest)
    print(f"Number of closest set points to try to link is {NB_CLOSEST_TO_LINK}")

    global NB_PATHS_MIN_SELECTED
    if args.min_paths:
        NB_PATHS_MIN_SELECTED = int(args.min_paths)
    print(f"Number of paths between step points minimum is {NB_PATHS_MIN_SELECTED}")

    global WORST_PATH_COST
    if args.worst_path_cost:
        WORST_PATH_COST = int(args.worst_path_cost)
    print(f"Worst tolerated cost of paths between step points is {WORST_PATH_COST}")

    global CONTINUE_AFTER
    CONTINUE_AFTER = args.continue_after
    print(f"Continue is {CONTINUE_AFTER}")

    global TARGET
    if args.target:
        TARGET = int(args.target)
        print(f"Target score is {TARGET}")

    start_time = time.time()
    grid = Grid(file_name)

    # create a reference grid
    file_name = f"Riders_ref.png"
    picture = Picture(grid, file_name, True)
    legend = f"For reference..."
    picture.put_legend(legend)
    picture.output()

    if args.search_paths:
        step1 = grid.step_point_from_name(args.search_paths[0])
        assert step1 is not None, f"No such step point as {args.search_paths[0]}"
        step2 = grid.step_point_from_name(args.search_paths[1])
        assert step2 is not None, f"No such step point as {args.search_paths[1]}"

        print(f"Searching at least {NB_PATHS_MIN_SELECTED} best path(s) costing at most {WORST_PATH_COST} between {step1} and {step2}...")
        paths = grid.extract_paths(step1, step2, NB_PATHS_MIN_SELECTED, WORST_PATH_COST)
        print("outputing the paths")
        for num_path, path in enumerate(paths):
            file_name = f"Riders_path_{step1}_{step2}_{num_path}.png"
            picture = Picture(grid, file_name, True)
            picture.put_path(path)
            legend = f"Cost = {path.cost} moves={len(path.content)}"
            picture.put_legend(legend)
            picture.output()

        sys.exit(0)

    impeached_pairs: typing.List[Pair] = list()
    if args.impeached_pairs is not None:

        assert len(args.impeached_pairs) % 2 == 0, "Please provide a pair number of steps for impeached paths"
        for num, step in enumerate(args.impeached_pairs):
            if num % 2 == 0:
                from_step1 = grid.step_point_from_name(step)
                assert from_step1 is not None, f"No such step point as {step}"
            else:
                to_step1 = grid.step_point_from_name(step)
                assert to_step1 is not None, f"No such step point as {step}"
                print(f"Will impeach paths between {from_step1} and {to_step1}...")
                assert from_step1 is not None
                impeached_pair = Pair(from_step1, to_step1)
                impeached_pairs.append(impeached_pair)

    grid.calc_best_paths(impeached_pairs)
    grid.calc_conflict_paths()

    forced_start_pairs: typing.List[Pair] = list()
    if args.forced_start_pairs is not None:

        assert len(args.forced_start_pairs) >= 2, "Please provide at least two steps for forced start paths"

        from_step2: typing.Optional[StepPoint] = None
        for num, step in enumerate(args.forced_start_pairs):
            if from_step2 is None:
                from_step2 = grid.step_point_from_name(step)
                assert from_step2 is not None, f"No such step point as {step}"
            else:
                to_step2 = grid.step_point_from_name(step)
                assert to_step2 is not None, f"No such step point as {step}"
                assert from_step2 != to_step2, "Please provide a list of dictinct steps"
                print(f"Will force path between {from_step2} and {to_step2}...")
                forced_pair = Pair(from_step2, to_step2)
                forced_start_pairs.append(forced_pair)
                from_step2 = to_step2

    forced_start: typing.Optional[StepPoint] = None
    if args.forced_start is not None:
        forced_start = grid.step_point_from_name(args.forced_start)
        assert forced_start is not None, f"No such step point as {args.forced_start}"
        print(f"Will force start on {forced_start}...")

    start_step = forced_start if forced_start is not None else grid.calc_starting_step_point()

    encouraged_pairs: typing.Set[Pair] = set()
    if args.encouraged_pairs is not None:

        assert len(args.encouraged_pairs) % 2 == 0, "Please provide a pair number of steps for encouraged paths"
        for num, step in enumerate(args.encouraged_pairs):
            if num % 2 == 0:
                from_step1 = grid.step_point_from_name(step)
                assert from_step1 is not None, f"No such step point as {step}"
            else:
                to_step1 = grid.step_point_from_name(step)
                assert to_step1 is not None, f"No such step point as {step}"
                print(f"Will encourage paths between {from_step1} and {to_step1}...")
                assert from_step1 is not None
                encouraged_pair = Pair(from_step1, to_step1)
                encouraged_pairs.add(encouraged_pair)

    circuit = grid.calc_complete_circuit(start_step, forced_start_pairs, encouraged_pairs, TARGET)

    if circuit is None:
        print("Failed!")
        sys.exit(1)

    grid.stats_paths(circuit)

    score = circuit.score()
    print(f"Success with score={score}!")
    circuit.show(f"Riders_detailed_{score.cost}_{score.size}.png", True)   # with debug info
    circuit.show(f"Riders_{score.cost}_{score.size}.png", False)  # for delivery

    end_time = time.time()
    elapsed = int(end_time - start_time)
    print(f"Elapsed = {elapsed//60}min {elapsed%60}sec")


if __name__ == '__main__':

    # this if script too slow and profile it
    if PROFILE:
        PR = cProfile.Profile()
        PR.enable()  # uncomment to have profile stats

    main()

    if PROFILE:
        PR.disable()
        # stats
        PS = pstats.Stats(PR)
        PS.strip_dirs()
        PS.sort_stats('time')
        PS.print_stats()  # uncomment to have profile stats

    sys.exit(0)
