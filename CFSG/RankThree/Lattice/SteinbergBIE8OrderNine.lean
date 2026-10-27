module

public import CFSG.RankThree.Lattice.SteinbergBIPrimeKernel

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley Matrix Polynomial

@[expose] def e8O9W : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  wordMat .E8 [4, 5, 2, 1, 3, 4, 1, 3, 1, 0]

@[expose] def e8O9Alpha : Fin Tag.E8.rank → ℤ := ![0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def e8O9Theta : Fin Tag.E8.rank → ℤ := ![2, 3, 4, 6, 5, 4, 3, 1]

@[expose] def e8O9Beta : Fin Tag.E8.rank → ℤ := ![0, 0, 0, 0, 0, 0, 1, 0]

@[expose] def e8O9Cols : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ :=
  fun j => if (j : ℕ) = 0 then e8O9Alpha else if (j : ℕ) = 1 then e8O9Theta else
    (e8O9W ^ ((j : ℕ) - 2)) *ᵥ e8O9Beta

@[expose] def e8O9V : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  wordMat .E8 [6, 7, 5, 6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3,
    2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3]

@[expose] def e8O9AlphaList : List ℤ := [0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def e8O9ThetaList : List ℤ := [2, 3, 4, 6, 5, 4, 3, 1]

@[expose] def e8O9BetaList : List ℤ := [0, 0, 0, 0, 0, 0, 1, 0]

@[expose] def e8O9AlphaThetaList : List ℤ := [2, 3, 4, 6, 5, 4, 3, 2]

@[expose] def e8O9WList : List (List ℤ) :=
  [[-1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, -1, 1, 0, 0], [-1, 0, 2, -1, 0, 1, 0, 0],
   [0, 0, 2, -1, 0, 1, 0, 0], [0, 0, 2, -1, 0, 0, 1, 0], [0, -1, 1, 0, 0, 0, 1, 0],
   [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]]

@[expose] def e8O9BasisInv : List (List ℤ) :=
  [[0, 0, 1, -1, 1, -1, 0, 1], [0, 0, -1, 1, -1, 1, 0, 0], [0, 1, 1, -1, 0, -1, 1, 0],
   [0, 0, 0, -1, 2, -1, 0, 0], [0, -2, 0, 1, 0, 0, 0, 0], [0, 1, 1, -1, -1, 1, 0, 0],
   [-1, 1, 1, -1, 1, -1, 0, 0], [1, -1, 0, 0, 1, -1, 0, 0]]

@[expose] def e8O9BasisOps : List (ℕ × ℕ × ℤ) :=
  [(5, 0, 1), (0, 5, -1), (5, 0, 1), (0, 1, -2), (0, 6, -1), (0, 7, -2), (1, 6, -1), (4, 2, 1),
   (2, 4, -1), (4, 2, 1), (2, 6, -1), (2, 7, 1), (6, 3, 1), (3, 6, -1), (6, 3, 1), (3, 7, 1),
   (6, 4, 1), (4, 6, -1), (6, 4, 1), (4, 7, -1), (7, 5, 1), (5, 7, -1), (7, 5, 1)]

@[expose] def e8O9Rows : List KernelRow := [
  { rep := [-2, -3, -4, -6, -5, -4, -2, -1], fc := [0, -1],
    f := [1, 0, 0, 0, 0, 0], h := [1, 0, 0, 0, 0, 0], d := 1,
    q := [],
    orbit := [[-2, -3, -4, -6, -5, -4, -2, -1], [-2, -3, -4, -6, -4, -3, -2, -1],
       [-2, -3, -3, -5, -4, -3, -2, -1], [-1, -2, -2, -4, -3, -2, -2, -1],
       [-1, -1, -1, -2, -2, -2, -2, -1], [0, -1, -1, -2, -2, -2, -2, -1],
       [-1, -1, -2, -2, -2, -2, -2, -1], [-1, -2, -3, -4, -4, -3, -2, -1],
       [-2, -2, -4, -5, -4, -3, -2, -1], [2, 3, 4, 6, 5, 4, 2, 1], [2, 3, 4, 6, 4, 3, 2, 1],
       [2, 3, 3, 5, 4, 3, 2, 1], [1, 2, 2, 4, 3, 2, 2, 1], [1, 1, 1, 2, 2, 2, 2, 1],
       [0, 1, 1, 2, 2, 2, 2, 1], [1, 1, 2, 2, 2, 2, 2, 1], [1, 2, 3, 4, 4, 3, 2, 1],
       [2, 2, 4, 5, 4, 3, 2, 1]] },
  { rep := [-2, -3, -4, -6, -5, -3, -2, -1], fc := [-1, 0],
    f := [0, -1, 0, 1, -1, -1], h := [0, 0, 0, -1, 0, -1], d := 1,
    q := [-1, 0, 0, 1, 1],
    orbit := [[-2, -3, -4, -6, -5, -3, -2, -1], [-2, -2, -3, -5, -4, -3, -2, -1],
       [-1, -2, -2, -4, -3, -3, -2, -1], [-1, -2, -2, -3, -2, -2, -2, -1],
       [-1, -2, -2, -3, -3, -2, -2, -1], [-1, -1, -2, -3, -3, -2, -2, -1],
       [-1, -1, -2, -3, -3, -3, -2, -1], [-1, -2, -3, -4, -3, -3, -2, -1],
       [-2, -3, -4, -5, -4, -3, -2, -1], [2, 3, 4, 6, 5, 3, 2, 1], [2, 2, 3, 5, 4, 3, 2, 1],
       [1, 2, 2, 4, 3, 3, 2, 1], [1, 2, 2, 3, 2, 2, 2, 1], [1, 2, 2, 3, 3, 2, 2, 1],
       [1, 1, 2, 3, 3, 2, 2, 1], [1, 1, 2, 3, 3, 3, 2, 1], [1, 2, 3, 4, 3, 3, 2, 1],
       [2, 3, 4, 5, 4, 3, 2, 1]] },
  { rep := [-2, -2, -3, -4, -4, -3, -2, -1], fc := [-1, 0],
    f := [0, -1, 0, 0, 0, -1], h := [1, 1, 1, 1, 0, 0], d := 1,
    q := [-1, -1, -1],
    orbit := [[-2, -2, -3, -4, -4, -3, -2, -1], [-1, -2, -3, -5, -4, -3, -2, -1],
       [-2, -2, -3, -4, -3, -3, -2, -1], [-1, -3, -3, -5, -4, -3, -2, -1],
       [-2, -2, -3, -4, -3, -2, -2, -1], [-1, -2, -2, -4, -4, -3, -2, -1],
       [-1, -1, -2, -3, -2, -2, -2, -1], [-1, -2, -2, -3, -3, -3, -2, -1],
       [-1, -2, -3, -4, -3, -2, -2, -1], [2, 2, 3, 4, 4, 3, 2, 1], [1, 2, 3, 5, 4, 3, 2, 1],
       [2, 2, 3, 4, 3, 3, 2, 1], [1, 3, 3, 5, 4, 3, 2, 1], [2, 2, 3, 4, 3, 2, 2, 1],
       [1, 2, 2, 4, 4, 3, 2, 1], [1, 1, 2, 3, 2, 2, 2, 1], [1, 2, 2, 3, 3, 3, 2, 1],
       [1, 2, 3, 4, 3, 2, 2, 1]] },
  { rep := [-2, -2, -3, -4, -3, -2, -1, -1], fc := [-1, 0],
    f := [0, 0, 0, 0, 0, -1], h := [0, 0, 0, 0, -1, 0], d := 1,
    q := [-1, 0, 0, 1],
    orbit := [[-2, -2, -3, -4, -3, -2, -1, -1], [-1, -2, -2, -4, -3, -2, -1, -1],
       [-1, -1, -1, -2, -1, -1, -1, -1], [0, -1, 0, -1, -1, -1, -1, -1], [0, 0, 0, 0, 0, 0, -1, -1],
       [0, 0, 0, 0, -1, -1, -1, -1], [0, 0, -1, -1, -1, -1, -1, -1],
       [-1, -1, -2, -2, -2, -2, -1, -1], [-1, -2, -3, -4, -3, -2, -1, -1], [2, 2, 3, 4, 3, 2, 1, 1],
       [1, 2, 2, 4, 3, 2, 1, 1], [1, 1, 1, 2, 1, 1, 1, 1], [0, 1, 0, 1, 1, 1, 1, 1],
       [0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 1, 1, 1], [0, 0, 1, 1, 1, 1, 1, 1],
       [1, 1, 2, 2, 2, 2, 1, 1], [1, 2, 3, 4, 3, 2, 1, 1]] },
  { rep := [-2, -2, -3, -4, -3, -2, -1, 0], fc := [0, 0],
    f := [0, 0, 0, 0, 0, -1], h := [0, 0, 0, 0, -1, 0], d := 1,
    q := [-1, 0, 0, 1],
    orbit := [[-2, -2, -3, -4, -3, -2, -1, 0], [-1, -2, -2, -4, -3, -2, -1, 0],
       [-1, -1, -1, -2, -1, -1, -1, 0], [0, -1, 0, -1, -1, -1, -1, 0], [0, 0, 0, 0, 0, 0, -1, 0],
       [0, 0, 0, 0, -1, -1, -1, 0], [0, 0, -1, -1, -1, -1, -1, 0], [-1, -1, -2, -2, -2, -2, -1, 0],
       [-1, -2, -3, -4, -3, -2, -1, 0], [2, 2, 3, 4, 3, 2, 1, 0], [1, 2, 2, 4, 3, 2, 1, 0],
       [1, 1, 1, 2, 1, 1, 1, 0], [0, 1, 0, 1, 1, 1, 1, 0], [0, 0, 0, 0, 0, 0, 1, 0],
       [0, 0, 0, 0, 1, 1, 1, 0], [0, 0, 1, 1, 1, 1, 1, 0], [1, 1, 2, 2, 2, 2, 1, 0],
       [1, 2, 3, 4, 3, 2, 1, 0]] },
  { rep := [-1, -2, -2, -3, -3, -2, -1, -1], fc := [-1, 0],
    f := [0, -1, 1, 0, -1, 0], h := [1, 0, 0, 0, -1, -1], d := 1,
    q := [-1, -1, 1, 1],
    orbit := [[-1, -2, -2, -3, -3, -2, -1, -1], [-1, -1, -2, -3, -2, -1, -1, -1],
       [-1, -1, -1, -2, -2, -2, -1, -1], [0, -1, -1, -2, -1, -1, -1, -1],
       [-1, -1, -1, -1, -1, -1, -1, -1], [0, -1, -1, -2, -2, -1, -1, -1],
       [-1, 0, -1, -1, -1, -1, -1, -1], [0, -1, -1, -2, -2, -2, -1, -1],
       [-1, -1, -2, -2, -1, -1, -1, -1], [1, 2, 2, 3, 3, 2, 1, 1], [1, 1, 2, 3, 2, 1, 1, 1],
       [1, 1, 1, 2, 2, 2, 1, 1], [0, 1, 1, 2, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1],
       [0, 1, 1, 2, 2, 1, 1, 1], [1, 0, 1, 1, 1, 1, 1, 1], [0, 1, 1, 2, 2, 2, 1, 1],
       [1, 1, 2, 2, 1, 1, 1, 1]] },
  { rep := [-1, -2, -2, -3, -3, -2, -1, 0], fc := [0, 0],
    f := [0, -1, 1, 0, -1, 0], h := [1, 0, 0, 0, -1, -1], d := 1,
    q := [-1, -1, 1, 1],
    orbit := [[-1, -2, -2, -3, -3, -2, -1, 0], [-1, -1, -2, -3, -2, -1, -1, 0],
       [-1, -1, -1, -2, -2, -2, -1, 0], [0, -1, -1, -2, -1, -1, -1, 0],
       [-1, -1, -1, -1, -1, -1, -1, 0], [0, -1, -1, -2, -2, -1, -1, 0],
       [-1, 0, -1, -1, -1, -1, -1, 0], [0, -1, -1, -2, -2, -2, -1, 0],
       [-1, -1, -2, -2, -1, -1, -1, 0], [1, 2, 2, 3, 3, 2, 1, 0], [1, 1, 2, 3, 2, 1, 1, 0],
       [1, 1, 1, 2, 2, 2, 1, 0], [0, 1, 1, 2, 1, 1, 1, 0], [1, 1, 1, 1, 1, 1, 1, 0],
       [0, 1, 1, 2, 2, 1, 1, 0], [1, 0, 1, 1, 1, 1, 1, 0], [0, 1, 1, 2, 2, 2, 1, 0],
       [1, 1, 2, 2, 1, 1, 1, 0]] },
  { rep := [-1, -2, -2, -3, -2, -2, -1, -1], fc := [0, -1],
    f := [0, 1, 1, -1, 0, 1], h := [1, -1, 0, 0, -1, 0], d := 1,
    q := [-1, 1, 0, -1],
    orbit := [[-1, -2, -2, -3, -2, -2, -1, -1], [-1, -2, -2, -3, -2, -1, -1, -1],
       [-1, -1, -1, -2, -2, -1, -1, -1], [0, 0, 0, -1, -1, -1, -1, -1], [0, 0, 0, 0, 0, -1, -1, -1],
       [0, -1, -1, -1, -1, -1, -1, -1], [-1, -1, -2, -2, -2, -1, -1, -1],
       [-1, -1, -2, -3, -3, -2, -1, -1], [-1, -1, -2, -3, -2, -2, -1, -1], [1, 2, 2, 3, 2, 2, 1, 1],
       [1, 2, 2, 3, 2, 1, 1, 1], [1, 1, 1, 2, 2, 1, 1, 1], [0, 0, 0, 1, 1, 1, 1, 1],
       [0, 0, 0, 0, 0, 1, 1, 1], [0, 1, 1, 1, 1, 1, 1, 1], [1, 1, 2, 2, 2, 1, 1, 1],
       [1, 1, 2, 3, 3, 2, 1, 1], [1, 1, 2, 3, 2, 2, 1, 1]] },
  { rep := [-1, -2, -2, -3, -2, -2, -1, 0], fc := [1, -1],
    f := [0, 1, 1, -1, 0, 1], h := [1, -1, 0, 0, -1, 0], d := 1,
    q := [-1, 1, 0, -1],
    orbit := [[-1, -2, -2, -3, -2, -2, -1, 0], [-1, -2, -2, -3, -2, -1, -1, 0],
       [-1, -1, -1, -2, -2, -1, -1, 0], [0, 0, 0, -1, -1, -1, -1, 0], [0, 0, 0, 0, 0, -1, -1, 0],
       [0, -1, -1, -1, -1, -1, -1, 0], [-1, -1, -2, -2, -2, -1, -1, 0],
       [-1, -1, -2, -3, -3, -2, -1, 0], [-1, -1, -2, -3, -2, -2, -1, 0], [1, 2, 2, 3, 2, 2, 1, 0],
       [1, 2, 2, 3, 2, 1, 1, 0], [1, 1, 1, 2, 2, 1, 1, 0], [0, 0, 0, 1, 1, 1, 1, 0],
       [0, 0, 0, 0, 0, 1, 1, 0], [0, 1, 1, 1, 1, 1, 1, 0], [1, 1, 2, 2, 2, 1, 1, 0],
       [1, 1, 2, 3, 3, 2, 1, 0], [1, 1, 2, 3, 2, 2, 1, 0]] },
  { rep := [-1, -2, -2, -3, -2, -1, 0, 0], fc := [0, 0],
    f := [0, 0, 1, 0, -1, 0], h := [1, -2, 1, -1, -1, -1], d := 3,
    q := [-3, 0, 1, 1],
    orbit := [[-1, -2, -2, -3, -2, -1, 0, 0], [-1, -1, -1, -2, -1, 0, 0, 0],
       [0, 0, 1, 0, 0, 0, 0, 0], [1, 1, 2, 2, 2, 1, 0, 0], [1, 1, 2, 3, 2, 1, 0, 0],
       [1, 1, 1, 2, 1, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0], [0, 0, -1, -1, -1, -1, 0, 0],
       [-1, -1, -2, -2, -1, -1, 0, 0], [1, 2, 2, 3, 2, 1, 0, 0], [1, 1, 1, 2, 1, 0, 0, 0],
       [0, 0, -1, 0, 0, 0, 0, 0], [-1, -1, -2, -2, -2, -1, 0, 0], [-1, -1, -2, -3, -2, -1, 0, 0],
       [-1, -1, -1, -2, -1, -1, 0, 0], [0, -1, 0, -1, 0, 0, 0, 0], [0, 0, 1, 1, 1, 1, 0, 0],
       [1, 1, 2, 2, 1, 1, 0, 0]] },
  { rep := [-1, -1, -2, -2, -1, 0, 0, 0], fc := [-1, 1],
    f := [-1, 0, 0, 0, -1, -1], h := [0, 1, -1, 0, -1, -2], d := 3,
    q := [-3, -1, 1, 3, 2],
    orbit := [[-1, -1, -2, -2, -1, 0, 0, 0], [-1, -1, -1, -2, -2, -1, 0, 0],
       [0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 1, 1, 1, 0, 0, 0], [1, 0, 1, 1, 1, 1, 0, 0],
       [0, 1, 1, 2, 1, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0],
       [0, -1, -1, -1, -1, -1, 0, 0], [1, 1, 2, 2, 1, 0, 0, 0], [1, 1, 1, 2, 2, 1, 0, 0],
       [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, -1, -1, -1, 0, 0, 0], [-1, 0, -1, -1, -1, -1, 0, 0],
       [0, -1, -1, -2, -1, -1, 0, 0], [-1, -1, -1, -1, 0, 0, 0, 0], [0, -1, 0, -1, -1, 0, 0, 0],
       [0, 1, 1, 1, 1, 1, 0, 0]] },
  { rep := [-1, -1, -1, -1, -1, -1, 0, 0], fc := [0, 0],
    f := [0, 0, 1, -1, 0, 0], h := [2, -1, -1, 1, -2, -2], d := 3,
    q := [-3, 0, 2],
    orbit := [[-1, -1, -1, -1, -1, -1, 0, 0], [0, -1, -1, -2, -1, 0, 0, 0],
       [-1, 0, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0, 0], [0, 1, 1, 2, 2, 1, 0, 0],
       [1, 0, 1, 1, 0, 0, 0, 0], [0, 1, 0, 1, 1, 1, 0, 0], [0, 0, 0, 0, -1, -1, 0, 0],
       [0, 0, -1, -1, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 0, 0], [0, 1, 1, 2, 1, 0, 0, 0],
       [1, 0, 0, 0, 0, 0, 0, 0], [-1, 0, -1, 0, 0, 0, 0, 0], [0, -1, -1, -2, -2, -1, 0, 0],
       [-1, 0, -1, -1, 0, 0, 0, 0], [0, -1, 0, -1, -1, -1, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0],
       [0, 0, 1, 1, 0, 0, 0, 0]] },
  { rep := [-1, -1, -1, -1, -1, 0, 0, 0], fc := [-1, 1],
    f := [-1, -1, 1, 0, -1, -1], h := [1, -2, -2, -1, -4, -1], d := 3,
    q := [-4, 1, 5, 5, 1],
    orbit := [[-1, -1, -1, -1, -1, 0, 0, 0], [0, 0, 0, -1, -1, 0, 0, 0], [0, 1, 1, 1, 1, 0, 0, 0],
       [1, 0, 1, 1, 1, 0, 0, 0], [0, 0, 0, 1, 1, 1, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0],
       [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0], [0, -1, -1, -1, 0, 0, 0, 0],
       [1, 1, 1, 1, 1, 0, 0, 0], [0, 0, 0, 1, 1, 0, 0, 0], [0, -1, -1, -1, -1, 0, 0, 0],
       [-1, 0, -1, -1, -1, 0, 0, 0], [0, 0, 0, -1, -1, -1, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0],
       [0, -1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0, 0]] }]

@[expose] def e8O9Basis : List (List ℤ) :=
  lcols Tag.E8.rank (e8O9AlphaList :: e8O9ThetaList :: lorbit Tag.E8.rank e8O9WList e8O9BetaList 6)

@[expose] def e8O9Conj : List (List ℤ) :=
  lmul Tag.E8.rank (lmul Tag.E8.rank e8O9BasisInv e8O9WList) e8O9Basis

@[expose] def e8O9ConjNeg : List (List ℤ) :=
  lmul Tag.E8.rank (lmul Tag.E8.rank e8O9BasisInv (lsmul Tag.E8.rank (-1) e8O9WList)) e8O9Basis

theorem e8O9W_eq : e8O9W = toMat Tag.E8.rank e8O9WList :=
  wordMat_eq_toMat .E8 _ (by decide +kernel)

theorem e8O9Alpha_eq : e8O9Alpha = toVec Tag.E8.rank e8O9AlphaList := by decide +kernel

theorem e8O9Theta_eq : e8O9Theta = toVec Tag.E8.rank e8O9ThetaList := by decide +kernel

theorem e8O9Beta_eq : e8O9Beta = toVec Tag.E8.rank e8O9BetaList := by decide +kernel

theorem e8O9Cols_eq' : e8O9Cols = fun j : Fin Tag.E8.rank => toVec Tag.E8.rank
    ((e8O9AlphaList :: e8O9ThetaList ::
      lorbit Tag.E8.rank e8O9WList e8O9BetaList 6).getD j []) := by
  have h := cols_ite_two_eq (n := Tag.E8.rank) e8O9WList e8O9AlphaList e8O9ThetaList
    e8O9BetaList 6
  rw [← e8O9Alpha_eq, ← e8O9Theta_eq, ← e8O9Beta_eq, ← e8O9W_eq] at h
  exact h

theorem e8O9Cols_eq :
    (Matrix.of fun i (j : Fin Tag.E8.rank) => e8O9Cols j i) = toMat Tag.E8.rank e8O9Basis := by
  rw [e8O9Basis, ← of_cols_eq_toMat, e8O9Cols_eq']

theorem e8O9Basis_mul_inv : lmul Tag.E8.rank e8O9Basis e8O9BasisInv = lid Tag.E8.rank := by
  decide +kernel

theorem e8O9_det_basis : (toMat Tag.E8.rank e8O9Basis).det = -1 := by
  rw [det_toMat_eq_of_colAdds _ e8O9BasisOps (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem e8O9Conj_blocks :
    lowerLeftZero 2 6 e8O9Conj = true ∧ ltopLeft 2 e8O9Conj = [[1, 0], [0, 1]] ∧
      lbotRight 2 6 e8O9Conj = [[0, 0, 0, 0, 0, -1], [1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0],
        [0, 0, 1, 0, 0, -1], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0]] := by
  decide +kernel

theorem e8O9ConjNeg_blocks :
    lowerLeftZero 2 6 e8O9ConjNeg = true ∧ ltopLeft 2 e8O9ConjNeg = [[-1, 0], [0, -1]] ∧
      lbotRight 2 6 e8O9ConjNeg = [[0, 0, 0, 0, 0, 1], [-1, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0],
        [0, 0, -1, 0, 0, 1], [0, 0, 0, -1, 0, 0], [0, 0, 0, 0, -1, 0]] := by
  decide +kernel

theorem charpoly_e8O9W : e8O9W.charpoly = (X - 1) ^ 2 * (X ^ 6 + X ^ 3 + 1) := by
  have hc : (toMat Tag.E8.rank e8O9WList).charpoly = (toMat Tag.E8.rank e8O9Conj).charpoly := by
    rw [charpoly_eq_of_conj (B := toMat Tag.E8.rank e8O9Basis)
      (B' := toMat Tag.E8.rank e8O9BasisInv)
      (by rw [← toMat_lmul, e8O9Basis_mul_inv, toMat_lid]), e8O9Conj, toMat_lmul, toMat_lmul]
  obtain ⟨h₁, h₂, h₃⟩ := e8O9Conj_blocks
  have hb := charpoly_eq_mul_of_blocks (k := 2) (m := 6) e8O9Conj h₁
  rw [h₂, h₃, charpoly_toMat_two_diag, map_one] at hb
  rw [e8O9W_eq, hc]
  refine Eq.trans (hb : (toMat Tag.E8.rank e8O9Conj).charpoly = _) (congrArg _ ?_)
  exact charpoly_eq_of_lists (cs := [1, 0, 0, 1, 0, 0, 1]) (by monicity!) (by compute_degree!)
    (by simp [polyOfList]; ring) (by decide +kernel) [1, 0, 0, 0, 0, 0]
    (by rw [orbitMat_eq_toMat]; exact isUnit_det_of_lmul_eq_lid (N := lid 6) (by decide +kernel))

theorem charpoly_neg_e8O9W : (-e8O9W).charpoly = (X + 1) ^ 2 * (X ^ 6 - X ^ 3 + 1) := by
  have hc : (toMat Tag.E8.rank (lsmul Tag.E8.rank (-1) e8O9WList)).charpoly =
      (toMat Tag.E8.rank e8O9ConjNeg).charpoly := by
    rw [charpoly_eq_of_conj (B := toMat Tag.E8.rank e8O9Basis)
      (B' := toMat Tag.E8.rank e8O9BasisInv)
      (by rw [← toMat_lmul, e8O9Basis_mul_inv, toMat_lid]), e8O9ConjNeg, toMat_lmul, toMat_lmul]
  obtain ⟨h₁, h₂, h₃⟩ := e8O9ConjNeg_blocks
  have hb := charpoly_eq_mul_of_blocks (k := 2) (m := 6) e8O9ConjNeg h₁
  rw [h₂, h₃, charpoly_toMat_two_diag, show (C (-1 : ℤ)) = -1 by simp, sub_neg_eq_add] at hb
  rw [e8O9W_eq, ← toMat_lsmul_neg_one, hc]
  refine Eq.trans (hb : (toMat Tag.E8.rank e8O9ConjNeg).charpoly = _) (congrArg _ ?_)
  exact charpoly_eq_of_lists (cs := [1, 0, 0, -1, 0, 0, 1]) (by monicity!) (by compute_degree!)
    (by simp [polyOfList]; ring) (by decide +kernel) [1, 0, 0, 0, 0, 0]
    (by
      rw [orbitMat_eq_toMat]
      exact isUnit_det_of_lmul_eq_lid (N := lcols 6 (lorbit 6 [[0, 0, 0, 0, 0, 1],
        [-1, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0], [0, 0, -1, 0, 0, 1], [0, 0, 0, -1, 0, 0],
          [0, 0, 0, 0, -1, 0]] [1, 0, 0, 0, 0, 0] 6)) (by decide +kernel))

theorem e8O9_root_kernel (p : ℕ) [Fact p.Prime] (hp3 : 3 < p) (a : ZMod p)
    (ha : a ^ 6 + a ^ 3 + 1 = 0) (z : Fin Tag.E8.rank → ZMod p)
    (hz0 : z ≠ 0) (hz : (e8O9W.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = a • z) :
    {r | IsRoot .E8 r ∧ pair r z = 0} =
      {e8O9Alpha, -e8O9Alpha, e8O9Theta, -e8O9Theta, e8O9Alpha + e8O9Theta,
        -(e8O9Alpha + e8O9Theta)} := by
  rw [e8O9W_eq] at hz
  have hΦ : peval [1, 0, 0, 1, 0, 0, 1] a = 0 := by
    simp only [peval_cons, peval_nil, Int.cast_one, Int.cast_zero]
    linear_combination ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    norm_num at ha
  have ha1 : a ≠ 1 := by
    rintro rfl
    have h3 : ((3 : ℤ) : ZMod p) ≠ 0 := intCast_zmod_ne_zero (by norm_num) (by exact_mod_cast hp3)
    apply h3
    push_cast
    linear_combination ha
  have hα : pair (toVec Tag.E8.rank e8O9AlphaList) z = 0 :=
    pair_eq_zero_of_fixed hz ha1 (by rw [← toVec_lmulVec]; exact congrArg _ (by decide +kernel))
  have hθ : pair (toVec Tag.E8.rank e8O9ThetaList) z = 0 :=
    pair_eq_zero_of_fixed hz ha1 (by rw [← toVec_lmulVec]; exact congrArg _ (by decide +kernel))
  have hαθ : pair (toVec Tag.E8.rank e8O9AlphaThetaList) z = 0 := by
    have h : toVec Tag.E8.rank e8O9AlphaThetaList =
        toVec Tag.E8.rank e8O9AlphaList + toVec Tag.E8.rank e8O9ThetaList := by
      decide +kernel
    rw [h, pair_add, hα, hθ, add_zero]
  have hβ : pair (toVec Tag.E8.rank e8O9BetaList) z ≠ 0 := by
    intro h0
    apply hz0
    refine eq_zero_of_pair_cols_eq_zero (B := toMat Tag.E8.rank e8O9Basis)
      (by rw [e8O9_det_basis]; exact isUnit_one.neg) fun j => ?_
    have hcol : (fun i => toMat Tag.E8.rank e8O9Basis i j) = toVec Tag.E8.rank
        ((e8O9AlphaList :: e8O9ThetaList ::
          lorbit Tag.E8.rank e8O9WList e8O9BetaList 6).getD j []) := by
      rw [← e8O9Cols_eq]
      exact congrFun e8O9Cols_eq' j
    rw [hcol, getD_cons_eq_ite, getD_cons_eq_ite]
    have hj : (j : ℕ) < 8 := j.isLt
    split_ifs with h h'
    · exact hα
    · exact hθ
    · rw [toVec_lorbit_getD (by omega), pair_pow_mulVec hz, h0, mul_zero]
  have hd : ∀ r ∈ e8O9Rows, 0 < r.d ∧ r.d ≤ 3 := by decide +kernel
  have hker := rootKernel_eq_of_rows (τ := .E8) (F := [e8O9AlphaList, e8O9ThetaList])
    (β := e8O9BetaList) (Φ := [1, 0, 0, 1, 0, 0, 1]) (m := 9) (signed := true) e8O9Rows
    [e8O9AlphaList, vneg Tag.E8.rank e8O9AlphaList, e8O9ThetaList, vneg Tag.E8.rank e8O9ThetaList,
      e8O9AlphaThetaList, vneg Tag.E8.rank e8O9AlphaThetaList]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hz ha0 hΦ
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hα
      · exact hθ) hβ
    (fun r hr => intCast_zmod_ne_zero (hd r hr).1 (by
      have h2 : (3 : ℤ) < p := by exact_mod_cast hp3
      have := (hd r hr).2
      omega))
    (by
      intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hα
      · rw [toVec_vneg, pair_neg, hα]
        exact neg_zero
      · exact hθ
      · rw [toVec_vneg, pair_neg, hθ]
        exact neg_zero
      · exact hαθ
      · rw [toVec_vneg, pair_neg, hαθ]
        exact neg_zero)
  refine hker.trans ?_
  have hsum : e8O9Alpha + e8O9Theta = toVec Tag.E8.rank e8O9AlphaThetaList := by decide +kernel
  ext r
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left, Set.mem_insert_iff, Set.mem_singleton_iff, toVec_vneg, ← e8O9Alpha_eq,
    ← e8O9Theta_eq, hsum]

theorem E8_order_nine_lattice_coupled_torus_and_exact_A2_root_kernel :
    IsRoot .E8 e8O9Alpha ∧ IsRoot .E8 e8O9Theta ∧
    e8O9Alpha ⬝ᵥ (Tag.E8.cartan *ᵥ e8O9Theta) = -1 ∧ orderOf e8O9W = 9 ∧
    e8O9W *ᵥ e8O9Alpha = e8O9Alpha ∧ e8O9W *ᵥ e8O9Theta = e8O9Theta ∧
    (LinearIndependent ℤ e8O9Cols ∧ Submodule.span ℤ (Set.range e8O9Cols) = ⊤) ∧
    (Matrix.of fun i (j : Fin Tag.E8.rank) => e8O9Cols j i).det = -1 ∧
    (e8O9W ^ 6 + e8O9W ^ 3 + 1) *ᵥ e8O9Beta = e8O9Theta - e8O9Alpha ∧
    e8O9W.charpoly = (X - 1) ^ 2 * (X ^ 6 + X ^ 3 + 1) ∧
    (-e8O9W).charpoly = (X + 1) ^ 2 * (X ^ 6 - X ^ 3 + 1) ∧
    (∀ p : ℕ, p.Prime → 3 < p → ∀ a : ZMod p, a ^ 6 + a ^ 3 + 1 = 0 →
      ∀ z : Fin Tag.E8.rank → ZMod p, z ≠ 0 →
        (e8O9W.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = a • z →
        {r | IsRoot .E8 r ∧ pair r z = 0} =
          {e8O9Alpha, -e8O9Alpha, e8O9Theta, -e8O9Theta, e8O9Alpha + e8O9Theta,
            -(e8O9Alpha + e8O9Theta)}) ∧
    e8O9V *ᵥ Pi.single 0 1 = e8O9Alpha ∧ e8O9V *ᵥ Pi.single 2 1 = e8O9Theta := by
  have hV : e8O9V = toMat Tag.E8.rank (lword Tag.E8.rank (cartanList .E8)
      [6, 7, 5, 6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2,
        1, 3, 4, 5, 0, 2, 3, 4, 1, 3]) :=
    wordMat_eq_toMat .E8 _ rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, charpoly_e8O9W, charpoly_neg_e8O9W,
    fun p hp hp3 a ha z hz0 hz => @e8O9_root_kernel p ⟨hp⟩ hp3 a ha z hz0 hz, ?_, ?_⟩
  · rw [e8O9Alpha_eq]
    exact isRoot_toVec (by decide +kernel)
  · rw [e8O9Theta_eq]
    exact isRoot_toVec (by decide +kernel)
  · rw [e8O9Alpha_eq, e8O9Theta_eq, ← toMat_cartanList, ← toVec_lmulVec]
    decide +kernel
  · rw [e8O9W_eq]
    exact orderOf_toMat_eq (by norm_num) (by decide +kernel) (by decide +kernel)
  · rw [e8O9W_eq, e8O9Alpha_eq, ← toVec_lmulVec]
    exact congrArg _ (by decide +kernel)
  · rw [e8O9W_eq, e8O9Theta_eq, ← toVec_lmulVec]
    exact congrArg _ (by decide +kernel)
  · rw [Module.Basis.is_basis_iff_det (Pi.basisFun ℤ (Fin Tag.E8.rank)), Module.Basis.det_apply]
    have h : (Pi.basisFun ℤ (Fin Tag.E8.rank)).toMatrix e8O9Cols =
        Matrix.of fun i (j : Fin Tag.E8.rank) => e8O9Cols j i := rfl
    rw [h, e8O9Cols_eq, e8O9_det_basis]
    exact isUnit_one.neg
  · rw [e8O9Cols_eq, e8O9_det_basis]
  · have h : e8O9W ^ 6 + e8O9W ^ 3 + 1 = toMat Tag.E8.rank (ladd Tag.E8.rank
        (ladd Tag.E8.rank (lpow Tag.E8.rank e8O9WList 6) (lpow Tag.E8.rank e8O9WList 3))
          (lid Tag.E8.rank)) := by
      rw [toMat_ladd, toMat_ladd, toMat_lpow, toMat_lpow, toMat_lid, e8O9W_eq]
    rw [h, e8O9Beta_eq, ← toVec_lmulVec, e8O9Theta_eq, e8O9Alpha_eq]
    decide +kernel
  · rw [hV, e8O9Alpha_eq, show (Pi.single 0 1 : Fin Tag.E8.rank → ℤ) =
      toVec Tag.E8.rank [1, 0, 0, 0, 0, 0, 0, 0] by decide +kernel, ← toVec_lmulVec]
    exact congrArg _ (by decide +kernel)
  · rw [hV, e8O9Theta_eq, show (Pi.single 2 1 : Fin Tag.E8.rank → ℤ) =
      toVec Tag.E8.rank [0, 0, 1, 0, 0, 0, 0, 0] by decide +kernel, ← toVec_lmulVec]
    exact congrArg _ (by decide +kernel)

end CFSG.RankThree.Lattice
