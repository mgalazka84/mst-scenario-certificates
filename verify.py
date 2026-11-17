"""Reproduce the finite checks in Certifying minimum spanning trees across cost scenarios.

Run with Python 3.10 or newer. All arithmetic and comparisons are exact integers.
"""
from collections import deque
from dataclasses import dataclass
from itertools import combinations, product
from random import Random
import argparse
import csv
import json
from pathlib import Path


@dataclass
class Instance:
    n: int
    edges: list                 # Edge index -> pair of vertices
    bounds: list                # Each entry is (lower, nominal, upper)
    costs: list                 # Measurement costs
    offsets: list               # Scenario -> vector indexed by edge
    trees: list                 # Scenario -> frozen set of nominal tree edges

    def candidates(self):
        return [i for i, (lo, _, hi) in enumerate(self.bounds) if lo < hi]


def subsets(items):
    items = sorted(items)
    for size in range(len(items) + 1):
        for group in combinations(items, size):
            yield frozenset(group)


def kruskal(n, edges, weights):
    parent = list(range(n))

    def root(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    chosen = []
    for i in sorted(range(len(edges)), key=lambda j: (weights[j], j)):
        a, b = edges[i]
        a, b = root(a), root(b)
        if a != b:
            parent[a] = b
            chosen.append(i)
            if len(chosen) == n - 1:
                break
    assert len(chosen) == n - 1
    return frozenset(chosen)


def make_instance(n, edges, bounds, costs, offsets):
    assert len(edges) == len(bounds) == len(costs)
    assert all(lo <= nom <= hi for lo, nom, hi in bounds)
    assert len(set(tuple(sorted(edge)) for edge in edges)) == len(edges)
    trees = []
    for offset in offsets:
        assert len(offset) == len(edges)
        weights = [b[1] + d for b, d in zip(bounds, offset)]
        trees.append(kruskal(n, edges, weights))
    return Instance(n, edges, bounds, costs, offsets, trees)


def tree_path(adjacency, start, end):
    prev = {start: None}
    todo = [start]
    while todo:
        u = todo.pop()
        if u == end:
            break
        for v, edge in adjacency[u]:
            if v not in prev:
                prev[v] = (u, edge)
                todo.append(v)
    path = []
    while end != start:
        end, edge = prev[end]
        path.append(edge)
    return path


def conflicts(instance):
    forced, pairs = set(), set()
    for tree, d in zip(instance.trees, instance.offsets):
        adjacency = [[] for _ in range(instance.n)]
        for i in tree:
            u, v = instance.edges[i]
            adjacency[u].append((v, i))
            adjacency[v].append((u, i))
        for f, (u, v) in enumerate(instance.edges):
            if f in tree:
                continue
            low_f, nominal_f, _ = instance.bounds[f]
            for e in tree_path(adjacency, u, v):
                _, nominal_e, high_e = instance.bounds[e]
                assert nominal_e + d[e] <= nominal_f + d[f]
                if high_e + d[e] > low_f + d[f]:
                    pairs.add(tuple(sorted((e, f))))
                if high_e + d[e] > nominal_f + d[f]:
                    forced.add(e)
                if nominal_e + d[e] > low_f + d[f]:
                    forced.add(f)
    return forced, {pair for pair in pairs if forced.isdisjoint(pair)}


def covers(query, forced, pairs):
    return forced <= query and all(u in query or v in query for u, v in pairs)


def adverse_oracle(instance, query):
    # The corner is chosen separately for each supplied tree.
    for tree, d in zip(instance.trees, instance.offsets):
        w = [(nominal if e in query else (hi if e in tree else lo)) + d[e]
             for e, (lo, nominal, hi) in enumerate(instance.bounds)]
        optimum = kruskal(instance.n, instance.edges, w)
        if sum(w[e] for e in optimum) < sum(w[e] for e in tree):
            return False
    return True


def list_spanning_trees(instance):
    # Deliberately independent of Kruskal, using connectivity of (n-1)-edge sets.
    trees = []
    for items in combinations(range(len(instance.edges)), instance.n - 1):
        adjacency = [[] for _ in range(instance.n)]
        for i in items:
            u, v = instance.edges[i]
            adjacency[u].append(v)
            adjacency[v].append(u)
        seen, todo = {0}, [0]
        while todo:
            for v in adjacency[todo.pop()]:
                if v not in seen:
                    seen.add(v)
                    todo.append(v)
        if len(seen) == instance.n:
            trees.append(items)
    return trees


def literal_oracle(instance, query, trees):
    options = [(nominal,) if e in query or lo == hi else (lo, hi)
               for e, (lo, nominal, hi) in enumerate(instance.bounds)]
    for base in product(*options):
        for given, d in zip(instance.trees, instance.offsets):
            w = [x + y for x, y in zip(base, d)]
            selected_cost = sum(w[e] for e in given)
            if any(sum(w[e] for e in rival) < selected_cost for rival in trees):
                return False
    return True


def bipartite_cover_cost(pairs, left, costs):
    # Source and sink have negative indices. All original edge indices are nonnegative.
    source, sink = -1, -2
    residual = {source: {}, sink: {}}
    vertices = set().union(*(set(edge) for edge in pairs)) if pairs else set()
    large = 1 + sum(costs[v] for v in vertices)

    def add(u, v, cap):
        residual.setdefault(u, {})[v] = cap
        residual.setdefault(v, {})[u] = 0

    for v in vertices:
        if v in left:
            add(source, v, costs[v])
        else:
            add(v, sink, costs[v])
    for u, v in pairs:
        if u not in left:
            u, v = v, u
        assert u in left and v not in left
        add(u, v, large)
    flow = 0
    while True:
        parent = {source: None}
        queue = deque([source])
        while queue and sink not in parent:
            u = queue.popleft()
            for v, cap in residual[u].items():
                if cap > 0 and v not in parent:
                    parent[v] = u
                    queue.append(v)
        if sink not in parent:
            return flow
        v, amount = sink, large
        while v != source:
            u = parent[v]
            amount = min(amount, residual[u][v])
            v = u
        v = sink
        while v != source:
            u = parent[v]
            residual[u][v] -= amount
            residual[v][u] += amount
            v = u
        flow += amount


def switch_algorithm(instance, forced, pairs):
    active = {v for pair in pairs for v in pair}
    switched = {v for v in active if len({v in t for t in instance.trees}) > 1}
    best = sum(instance.costs)
    for chosen in subsets(switched):
        excluded = switched - chosen
        if any(u in excluded and v in excluded for u, v in pairs):
            continue
        fixed = set(forced) | chosen
        for u, v in pairs:
            if u in excluded:
                fixed.add(v)
            if v in excluded:
                fixed.add(u)
        rest = {pair for pair in pairs if fixed.isdisjoint(pair)}
        extra = bipartite_cover_cost(rest, instance.trees[0], instance.costs)
        best = min(best, sum(instance.costs[e] for e in fixed) + extra)
    return best


def reduction_instance(n, original):
    stars, matching, heads = [], [], []
    total = n
    for u, v in original:
        a, b = total, total + 1
        stars.extend([(u, a), (b, v)])
        matching.append((a, b))
        heads.append(a)
        total += 2
    subdivided = stars + matching
    edges = [(total, v) for v in range(total)] + subdivided
    bounds = [(1, 3, 5)] * total + [(0, 0, 0)] * len(subdivided)
    offsets = []
    for active, centres in [(set(stars), set(range(n))),
                            (set(matching), set(range(n)) | set(heads))]:
        offsets.append([0 if v in centres else 3 for v in range(total)]
                       + [0 if e in active else 10 for e in subdivided])
    return make_instance(total + 1, edges, bounds, [1] * len(edges), offsets), subdivided


def reduction_checks():
    inputs = [
        ('P3', 3, [(0, 1), (1, 2)]),
        ('K3', 3, [(0, 1), (1, 2), (2, 0)]),
        ('K1,3', 4, [(0, i) for i in [1, 2, 3]]),
        ('C4', 4, [(0, 1), (1, 2), (2, 3), (3, 0)]),
        ('K4', 4, list(combinations(range(4), 2)))]
    rows = []
    for name, n, orig in inputs:
        inst, sub = reduction_instance(n, orig)
        tau = min(len(q) for q in subsets(range(n)) if covers(q, set(), orig))
        forced, pairs = conflicts(inst)
        assert not forced and pairs == {tuple(sorted(e)) for e in sub}
        optimum, total, good = len(inst.edges), 0, 0
        for q in subsets(inst.candidates()):
            ok = adverse_oracle(inst, q)
            assert ok == covers(q, set(), sub)
            total += 1
            if ok:
                optimum, good = min(optimum, len(q)), good + 1
        assert optimum == len(orig) + tau == switch_algorithm(inst, forced, pairs)
        rows.append(dict(graph=name, measurements=len(inst.candidates()),
                         subsets=total, certificates=good, optimum=optimum))
    return rows


def clique_instance(scenarios):
    count = 2 ** scenarios
    matching = [(2 * i, 2 * i + 1) for i in range(count)]
    matched = set(matching)
    fixed = [edge for edge in combinations(range(2 * count), 2) if edge not in matched]
    edges = matching + fixed
    bounds = [(1, 3, 5)] * count + [(0, 0, 0)] * len(fixed)
    offsets = []
    for bit in range(scenarios):
        path = [i for i in range(count) if (i >> bit) & 1 == 0]
        chords = sorted(set(range(count)) - set(path))
        groups = [[] for _ in range(len(path) + 1)]
        for j, i in enumerate(path):
            groups[j].append(2 * i)
            groups[j + 1].append(2 * i + 1)
        for i in chords:
            groups[0].append(2 * i)
            groups[-1].append(2 * i + 1)
        zero = {tuple(sorted((g[0], v))) for g in groups for v in g[1:]}
        offsets.append([0 if i in path else 3 for i in range(count)]
                       + [0 if e in zero else 10 for e in fixed])
    return make_instance(2 * count, edges, bounds, [1] * len(edges), offsets)


def clique_checks():
    results = []
    for s in (1, 2, 3):
        inst = clique_instance(s)
        n = len(inst.candidates())
        forced, pairs = conflicts(inst)
        assert not forced and pairs == set(combinations(range(n), 2))
        for q in subsets(range(n)):
            assert adverse_oracle(inst, q) == (len(q) >= n - 1)
        assert switch_algorithm(inst, forced, pairs) == n - 1
        results.append(dict(scenarios=s, clique=n, optimum=n - 1,
                            lp_numerator=n, lp_denominator=2))
    return results


def cycle_checks():
    n = 4
    ring = [(i, (i + 1) % n) for i in range(n)]
    graphs = list(subsets(combinations(range(n), 2)))
    checked, scenario_counts = 0, {}
    for target in graphs:
        centre_cover = min((q for q in subsets(range(n)) if covers(q, set(), target)),
                           key=len)
        stars = {c: set() for c in centre_cover}
        for u, v in sorted(target):
            centre, leaf = (u, v) if u in centre_cover else (v, u)
            stars[centre].add(leaf)
        offsets = [[6 if i == c else 3 if i in leaves else 0 for i in range(n)]
                   for c, leaves in sorted(stars.items()) if leaves]
        if not offsets:
            offsets = [[9, 0, 0, 0]]
        assert len(offsets) == max(1, len(centre_cover))
        scenario_counts[len(offsets)] = scenario_counts.get(len(offsets), 0) + 1
        inst = make_instance(n, ring, [(1, 3, 5)] * n, [1] * n, offsets)
        forced, pairs = conflicts(inst)
        assert not forced and pairs == set(target)
        for q in subsets(range(n)):
            assert adverse_oracle(inst, q) == covers(q, set(), target)
            checked += 1
    return dict(labelled_graphs=len(graphs), certificate_subsets=checked,
                minimum_scenario_histogram=scenario_counts)


def small_checks():
    rng = Random(1741)
    cases, tested, mandatory_cases, tied_cases = 150, 0, 0, 0
    for run in range(cases):
        n = rng.randint(3, 5)
        tree = [(rng.randrange(v), v) for v in range(1, n)]
        chords = sorted(set(combinations(range(n), 2)) - set(tree))
        m = rng.randint(n, min(6, n * (n - 1) // 2))
        edges = sorted(tree + rng.sample(chords, m - len(tree)))
        bounds = []
        for _ in edges:
            lo = rng.randrange(4)
            hi = lo + rng.randrange(5)
            bounds.append((lo, rng.randint(lo, hi), hi))
        costs = [rng.randint(1, 5) for _ in edges]
        offsets = [[rng.randrange(4) for _ in edges] for _ in range(1 + run % 3)]
        inst = make_instance(n, edges, bounds, costs, offsets)
        trees = list_spanning_trees(inst)
        has_tie = False
        for s, off in enumerate(offsets):
            w = [b[1] + d for b, d in zip(bounds, off)]
            values = [sum(w[i] for i in tr) for tr in trees]
            minimum = min(values)
            tied = [tr for tr, c in zip(trees, values) if c == minimum]
            has_tie |= len(tied) > 1
            inst.trees[s] = frozenset(rng.choice(tied))
        forced, pairs = conflicts(inst)
        mandatory_cases += int(bool(forced))
        tied_cases += int(has_tie)
        best = sum(costs)
        for q in subsets(inst.candidates()):
            literal = literal_oracle(inst, q, trees)
            assert literal == covers(q, forced, pairs) == adverse_oracle(inst, q)
            if literal:
                best = min(best, sum(costs[e] for e in q))
            tested += 1
        assert switch_algorithm(inst, forced, pairs) == best
    return dict(seed=1741, instances=cases, certificate_subsets=tested,
                with_mandatory=mandatory_cases, with_nominal_ties=tied_cases)


def cactus_optimum(instance):
    forced, pairs = conflicts(instance)
    reference = instance.trees[0]
    adjacency = [[] for _ in range(instance.n)]
    for i in reference:
        u, v = instance.edges[i]
        adjacency[u].append((v, i))
        adjacency[v].append((u, i))
    price = sum(instance.costs[i] for i in forced)
    seen_edges, accounted_pairs = set(), set()
    for f, (u, v) in enumerate(instance.edges):
        if f in reference:
            continue
        block = {f, *tree_path(adjacency, u, v)}
        assert block.isdisjoint(seen_edges), "Input must be a cactus"
        seen_edges.update(block)
        local = {(u, v) for u, v in pairs if u in block and v in block}
        accounted_pairs.update(local)
        active = {i for pair in local for i in pair}
        centres = {i for i in active if any(i not in tree for tree in instance.trees)}
        best = sum(instance.costs[i] for i in active)
        for chosen in subsets(centres):
            omitted = centres - chosen
            if any(a in omitted and b in omitted for a, b in local):
                continue
            picked = set(chosen)
            for a, b in local:
                if a in omitted:
                    picked.add(b)
                if b in omitted:
                    picked.add(a)
            assert covers(picked, set(), local)
            best = min(best, sum(instance.costs[i] for i in picked))
        price += best
    assert accounted_pairs == pairs
    return price


def cactus_checks():
    # The first two triangles meet at a vertex; a bridge leads to the third.
    edges = [(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (4, 2),
             (4, 5), (5, 6), (6, 7), (7, 5)]
    rng = Random(729)
    total = 0
    for run in range(30):
        bounds = []
        for _ in edges:
            low = rng.randrange(3)
            high = low + rng.randrange(5)
            bounds.append((low, rng.randint(low, high), high))
        costs = [rng.randint(1, 5) for _ in edges]
        tariffs = [[rng.randrange(5) for _ in edges] for _ in range(1 + run % 3)]
        instance = make_instance(8, edges, bounds, costs, tariffs)
        brute = sum(costs)
        for query in subsets(instance.candidates()):
            total += 1
            if adverse_oracle(instance, query):
                brute = min(brute, sum(costs[i] for i in query))
        assert cactus_optimum(instance) == brute
    return dict(seed=729, instances=30, certificate_subsets=total)


def example_check():
    inst = make_instance(3, [(0, 1), (1, 2), (2, 0)],
                         [(1, 3, 5)] * 3, [2, 3, 2],
                         [[6, 3, 0], [0, 3, 6]])
    trees = list_spanning_trees(inst)
    shared = [q for q in subsets(range(3)) if literal_oracle(inst, q, trees)]
    opt = min(sum(inst.costs[e] for e in q) for q in shared)
    assert opt == 3
    assert [q for q in shared if sum(inst.costs[e] for e in q) == opt] == [frozenset({1})]
    separate = set()
    for d in inst.offsets:
        single = make_instance(inst.n, inst.edges, inst.bounds, inst.costs, [d])
        cheapest = min((q for q in subsets(range(3)) if literal_oracle(single, q, trees)),
                       key=lambda q: sum(inst.costs[i] for i in q))
        separate.update(cheapest)
    separate_cost = sum(inst.costs[i] for i in separate)
    assert separate_cost == 4
    return dict(separate_union_cost=separate_cost, joint_cost=opt)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, help='Write summary.json and reduction.csv in this directory')
    args = parser.parse_args()
    results = dict(example=example_check(), reduction=reduction_checks(),
                   small=small_checks(), clique=clique_checks(), cycle=cycle_checks(),
                   cactus=cactus_checks())
    report = json.dumps(results, indent=2, ensure_ascii=False) + '\n'
    if args.out:
        args.out.mkdir(parents=True, exist_ok=True)
        (args.out / 'summary.json').write_text(report, encoding='utf-8')
        with (args.out / 'reduction.csv').open('w', newline='', encoding='utf-8') as f:
            rows = results['reduction']
            writer = csv.DictWriter(f, fieldnames=rows[0])
            writer.writeheader()
            writer.writerows(rows)
    print(report, end='')


if __name__ == '__main__':
    main()
