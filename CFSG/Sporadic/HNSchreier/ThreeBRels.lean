module

public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.Group.Basic

public section

namespace CFSG.Sporadic.HNSchreier.ThreeBRels

variable {G : Type*} [Group G]

@[expose] def xs (c : ℕ → G) (i : ℕ) : G :=
  [c 3, c 5, c 1 * c 0 * c 0, c 6 * c 1 * c 6 * c 4 * c 0].getD i 1

@[expose] def pw (z : G) (c : ℕ → G) (j : ℕ) : G :=
  [z, z * z, xs c 0, xs c 0 * xs c 0, xs c 1, xs c 1 * xs c 1, xs c 2, xs c 2 * xs c 2, xs c 3,
    xs c 3 * xs c 3].getD j 1

@[expose] def qa (c : ℕ → G) : G := c 6 * c 3 * c 0

@[expose] def qb (c : ℕ → G) : G := ([3, 2, 6, 6, 1, 0, 6, 6, 0, 0].map c).prod

@[expose] def nRows : List (ℕ × ℕ × List ℕ) :=
  [(0, 0, [0, 2, 7]), (0, 1, [4]), (0, 2, [6]), (0, 3, [1, 5, 7, 8]),
   (1, 0, [2, 7]), (1, 1, [4]), (1, 2, [6]), (1, 3, [0, 5, 7, 8]),
   (2, 0, [1, 2, 7]), (2, 1, [4]), (2, 2, [6]), (2, 3, [5, 7, 8]),
   (4, 0, [3]), (4, 1, [5]), (4, 2, [7]), (4, 3, [0, 9]),
   (6, 0, [1, 5, 7]), (6, 1, [0, 9]), (6, 2, [2, 6, 8]), (6, 3, [2, 4, 6])]

structure Rels (z y : G) (c : ℕ → G) : Prop where
  z_cube : z * z * z = 1
  z_ne : z ≠ 1
  x_cube : ∀ i < 4, xs c i * xs c i * xs c i = 1
  x13 : xs c 0 * xs c 2 = z * (xs c 2 * xs c 0)
  x14 : xs c 0 * xs c 3 = z * (xs c 3 * xs c 0)
  x24 : xs c 1 * xs c 3 = z * (xs c 3 * xs c 1)
  x34 : xs c 2 * xs c 3 = z * z * (xs c 3 * xs c 2)
  x12 : xs c 0 * xs c 1 = xs c 1 * xs c 0
  x23 : xs c 1 * xs c 2 = xs c 2 * xs c 1
  conj : ∀ r ∈ nRows, c r.1 * xs c r.2.1 = (r.2.2.map (pw z c)).prod * c r.1
  a_four : qa c * qa c * (qa c * qa c) = 1
  a_sq_ne : qa c * qa c ≠ 1
  b_sq : qb c * qb c = qa c * qa c
  aba : qa c * qb c * qa c = qb c
  a_sq_x : qa c * qa c * xs c 0 ≠ xs c 0 * (qa c * qa c)
  c0_cube : c 0 * c 0 * c 0 = 1
  y_x : y * xs c 0 ≠ xs c 0 * y

end CFSG.Sporadic.HNSchreier.ThreeBRels

end
