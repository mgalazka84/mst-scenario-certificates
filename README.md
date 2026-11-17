# Certifying minimum spanning trees across cost scenarios

Verification code and reference results for the article by Marek Gałązka and Hanna Wdowicka.

## Reproduction

The program uses only the Python standard library. It was tested with CPython 3.12.14. Clone or download the repository and run the following command from the directory containing this file.

```sh
python verify.py --out reproduced
```

The command prints a JSON summary and saves `reproduced/summary.json` and `reproduced/reduction.csv`. The corresponding reference files are in `results/`. Use a normal Python invocation so that assertions are enabled. The script uses no network access, external data, or optional solver. Omitting `--out` prints the report without writing files.

## Calculations

- The triangle example checks that the union of the two separately optimal certificates costs 4 and the unique joint optimum costs 3.
- Five two-scenario hardness instances are generated from the edge lists of a path, triangle, three-leaf star, four-cycle and complete graph on four vertices. Every one of the 71,296 measurement subsets is tested with an adverse-corner Kruskal computation, independently of the reduction and exchange graph.
- For 150 small graphs, the program enumerates spanning trees by connectivity and checks the endpoint completions of the box. It compares those decisions with the exchange graph and the adverse-corner oracle, and compares the least certificate price with the switching-edge algorithm. The graph, prices, bounds, offsets and tie choices are generated with seed 1741.
- For one, two and three scenarios, the clique construction is generated on a simple graph. The program checks all measurement subsets and all residual pairs. The reported fractional values are the analytic clique values, obtained by summing all pair inequalities and taking the all-half vector in the relaxation.
- All 64 labeled simple graphs on four vertices are encoded on the same four-edge cycle. Minimum unweighted covers for the construction are found by enumeration, and every resulting certificate family is checked.
- The cactus algorithm is tested on 30 instances on three triangles and a bridge with weighted measurements. Every candidate subset is checked by the adverse-corner oracle. The generator uses seed 729.

The function `make_instance` chooses a nominal minimum spanning tree by Kruskal's algorithm with edge-index tie breaking. In the mixed small-instance test a nominal minimizing tree is instead sampled explicitly among all minimizing trees. Base costs in an instance are triples (lower endpoint, nominal value, upper endpoint). A scenario adds one offset vector to the same base vector. All verification arithmetic is integral for these examples.
