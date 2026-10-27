module

public import CFSG.RankThree.Lattice.SteinbergBIPrimeKernel

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley Matrix Polynomial

@[expose] def e8O7W : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  wordMat .E8 [0, 2, 3, 4, 5, 6]

@[expose] def e8O7Theta : Fin Tag.E8.rank → ℤ := ![2, 3, 4, 6, 5, 4, 3, 2]

@[expose] def e8O7Beta : Fin Tag.E8.rank → ℤ := ![2, 2, 4, 5, 4, 3, 2, 1]

@[expose] def e8O7Cols : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ :=
  fun j => if (j : ℕ) = 0 then e8O7Theta else (e8O7W ^ ((j : ℕ) - 1)) *ᵥ e8O7Beta

@[expose] def e8O7Frame : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ :=
  ![![2, 3, 4, 6, 5, 4, 3, 2], ![-2, -2, -3, -4, -3, -2, -1, 0], ![0, -1, -1, -2, -2, -2, -1, 0],
    ![0, -1, -1, -2, -1, 0, 0, 0], ![0, -1, 0, 0, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, -1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, -1, 0]]

@[expose] def e8O7ThetaList : List ℤ := [2, 3, 4, 6, 5, 4, 3, 2]

@[expose] def e8O7BetaList : List ℤ := [2, 2, 4, 5, 4, 3, 2, 1]

@[expose] def e8O7FrameList : List (List ℤ) :=
  [[2, 3, 4, 6, 5, 4, 3, 2], [-2, -2, -3, -4, -3, -2, -1, 0], [0, -1, -1, -2, -2, -2, -1, 0],
    [0, -1, -1, -2, -1, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, 0, 0, -1, 0]]

@[expose] def e8O7WList : List (List ℤ) :=
  [[0, 1, 0, 0, 0, 0, -1, 1], [0, 1, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, -1, 1],
   [0, 1, 1, 0, 0, 0, -1, 1], [0, 0, 0, 1, 0, 0, -1, 1], [0, 0, 0, 0, 1, 0, -1, 1],
   [0, 0, 0, 0, 0, 1, -1, 1], [0, 0, 0, 0, 0, 0, 0, 1]]

@[expose] def e8O7BasisInv : List (List ℤ) :=
  [[0, -1, 0, 0, 0, 0, 0, 2], [0, 0, 1, -1, 1, -1, 1, -1], [-1, 0, 0, 1, -1, 1, -1, 0],
   [1, 0, -1, 0, 1, -1, 1, -1], [-1, 1, 1, -1, 0, 1, -1, 0], [1, 0, -1, 1, -1, 0, 1, -1],
   [-1, 1, 1, -1, 1, -1, 0, 0], [1, 0, -1, 1, -1, 1, -1, 0]]

@[expose] def e8O7BasisOps : List (ℕ × ℕ × ℤ) :=
  [(2, 0, 1), (0, 2, -1), (2, 0, 1), (0, 1, -2), (0, 2, 2), (0, 3, -1), (0, 4, -1), (0, 5, -1),
   (0, 6, -1), (0, 7, -2), (2, 1, 1), (1, 2, -1), (2, 1, 1), (1, 2, -2), (1, 7, 2), (3, 2, 1),
   (2, 3, -1), (3, 2, 1), (2, 3, 2), (2, 4, -1), (2, 5, -1), (2, 6, -1), (2, 7, 1), (3, 4, 1),
   (3, 5, 1), (3, 6, 1), (3, 7, -1), (4, 7, 1), (6, 5, 1), (5, 6, -1), (6, 5, 1), (7, 6, 1),
   (6, 7, -1), (7, 6, 1)]

@[expose] def e8O7Rows : List KernelRow := [
  { rep := [-2, -3, -4, -6, -5, -4, -3, -1], fc := [1],
    f := [-1, 0, -1, 0, -1, 0, 0], h := [0, 1, 1, 0, 0, 0], d := 1,
    q := [-1],
    orbit := [[-2, -3, -4, -6, -5, -4, -3, -1], [-1, -3, -3, -5, -4, -3, -2, -1],
       [-2, -3, -3, -5, -4, -3, -2, -1], [-2, -3, -4, -5, -4, -3, -2, -1],
       [-2, -3, -4, -6, -4, -3, -2, -1], [-2, -3, -4, -6, -5, -3, -2, -1],
       [-2, -3, -4, -6, -5, -4, -2, -1], [2, 3, 4, 6, 5, 4, 3, 1], [1, 3, 3, 5, 4, 3, 2, 1],
       [2, 3, 3, 5, 4, 3, 2, 1], [2, 3, 4, 5, 4, 3, 2, 1], [2, 3, 4, 6, 4, 3, 2, 1],
       [2, 3, 4, 6, 5, 3, 2, 1], [2, 3, 4, 6, 5, 4, 2, 1]] },
  { rep := [-2, -2, -4, -5, -4, -3, -2, -1], fc := [0],
    f := [-1, 0, 0, 0, 0, 0, 0], h := [-1, 0, 0, 0, 0, 0], d := 1,
    q := [],
    orbit := [[-2, -2, -4, -5, -4, -3, -2, -1], [-1, -2, -3, -5, -4, -3, -2, -1],
       [-1, -2, -2, -4, -4, -3, -2, -1], [-1, -2, -2, -3, -3, -3, -2, -1],
       [-1, -2, -2, -3, -2, -2, -2, -1], [-1, -2, -2, -3, -2, -1, -1, -1],
       [-2, -2, -3, -4, -3, -2, -1, -1], [2, 2, 4, 5, 4, 3, 2, 1], [1, 2, 3, 5, 4, 3, 2, 1],
       [1, 2, 2, 4, 4, 3, 2, 1], [1, 2, 2, 3, 3, 3, 2, 1], [1, 2, 2, 3, 2, 2, 2, 1],
       [1, 2, 2, 3, 2, 1, 1, 1], [2, 2, 3, 4, 3, 2, 1, 1]] },
  { rep := [-2, -2, -3, -5, -4, -3, -2, -1], fc := [0],
    f := [0, 0, -1, 1, -1, 1, -1], h := [0, -1, 0, 1, 0, -1], d := 1,
    q := [-1, 1, 0, 1, -2, 1],
    orbit := [[-2, -2, -3, -5, -4, -3, -2, -1], [-1, -2, -3, -4, -4, -3, -2, -1],
       [-1, -2, -2, -4, -3, -3, -2, -1], [-1, -2, -2, -3, -3, -2, -2, -1],
       [-1, -2, -2, -3, -2, -2, -1, -1], [-2, -2, -3, -4, -3, -2, -2, -1],
       [-1, -2, -3, -4, -3, -2, -1, -1], [2, 2, 3, 5, 4, 3, 2, 1], [1, 2, 3, 4, 4, 3, 2, 1],
       [1, 2, 2, 4, 3, 3, 2, 1], [1, 2, 2, 3, 3, 2, 2, 1], [1, 2, 2, 3, 2, 2, 1, 1],
       [2, 2, 3, 4, 3, 2, 2, 1], [1, 2, 3, 4, 3, 2, 1, 1]] },
  { rep := [-2, -2, -3, -4, -4, -3, -2, -1], fc := [0],
    f := [-1, 1, -1, 0, 0, 0, 0], h := [0, 1, 2, 2, 1, 0], d := 1,
    q := [-1],
    orbit := [[-2, -2, -3, -4, -4, -3, -2, -1], [-1, -2, -3, -4, -3, -3, -2, -1],
       [-1, -2, -2, -4, -3, -2, -2, -1], [-1, -2, -2, -3, -3, -2, -1, -1],
       [-2, -2, -3, -4, -3, -3, -2, -1], [-1, -2, -3, -4, -3, -2, -2, -1],
       [-1, -2, -2, -4, -3, -2, -1, -1], [2, 2, 3, 4, 4, 3, 2, 1], [1, 2, 3, 4, 3, 3, 2, 1],
       [1, 2, 2, 4, 3, 2, 2, 1], [1, 2, 2, 3, 3, 2, 1, 1], [2, 2, 3, 4, 3, 3, 2, 1],
       [1, 2, 3, 4, 3, 2, 2, 1], [1, 2, 2, 4, 3, 2, 1, 1]] },
  { rep := [-2, -2, -3, -4, -3, -2, -1, 0], fc := [2],
    f := [-1, 0, -1, 0, -1, 0, -1], h := [-1, -1, 0, 0, 0, 0], d := 1,
    q := [0, 1],
    orbit := [[-2, -2, -3, -4, -3, -2, -1, 0], [-1, -2, -3, -4, -3, -2, -1, 0],
       [-1, -2, -2, -4, -3, -2, -1, 0], [-1, -2, -2, -3, -3, -2, -1, 0],
       [-1, -2, -2, -3, -2, -2, -1, 0], [-1, -2, -2, -3, -2, -1, -1, 0],
       [-1, -2, -2, -3, -2, -1, 0, 0], [2, 2, 3, 4, 3, 2, 1, 0], [1, 2, 3, 4, 3, 2, 1, 0],
       [1, 2, 2, 4, 3, 2, 1, 0], [1, 2, 2, 3, 3, 2, 1, 0], [1, 2, 2, 3, 2, 2, 1, 0],
       [1, 2, 2, 3, 2, 1, 1, 0], [1, 2, 2, 3, 2, 1, 0, 0]] },
  { rep := [-1, -1, -2, -3, -3, -3, -2, -1], fc := [-1],
    f := [0, 0, 0, 0, 0, 1, 0], h := [0, 0, 1, 0, 0, 0], d := 1,
    q := [-1, 1],
    orbit := [[-1, -1, -2, -3, -3, -3, -2, -1], [0, -1, -1, -2, -2, -2, -2, -1],
       [0, -1, 0, -1, -1, -1, -1, -1], [-1, -1, -1, -1, -1, -1, -1, -1],
       [-1, -1, -2, -2, -1, -1, -1, -1], [-1, -1, -2, -3, -2, -1, -1, -1],
       [-1, -1, -2, -3, -3, -2, -1, -1], [1, 1, 2, 3, 3, 3, 2, 1], [0, 1, 1, 2, 2, 2, 2, 1],
       [0, 1, 0, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 2, 2, 1, 1, 1, 1],
       [1, 1, 2, 3, 2, 1, 1, 1], [1, 1, 2, 3, 3, 2, 1, 1]] },
  { rep := [-1, -1, -2, -3, -3, -2, -2, -1], fc := [-1],
    f := [-1, 1, -1, 1, 0, 0, 1], h := [1, 2, 1, 1, 2, 1], d := 1,
    q := [-2, 1, 1, -1, 1, 1],
    orbit := [[-1, -1, -2, -3, -3, -2, -2, -1], [0, -1, -1, -2, -2, -2, -1, -1],
       [-1, -1, -1, -2, -2, -2, -2, -1], [0, -1, -1, -1, -1, -1, -1, -1],
       [-1, -1, -1, -2, -1, -1, -1, -1], [-1, -1, -2, -2, -2, -1, -1, -1],
       [-1, -1, -2, -3, -2, -2, -1, -1], [1, 1, 2, 3, 3, 2, 2, 1], [0, 1, 1, 2, 2, 2, 1, 1],
       [1, 1, 1, 2, 2, 2, 2, 1], [0, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 2, 1, 1, 1, 1],
       [1, 1, 2, 2, 2, 1, 1, 1], [1, 1, 2, 3, 2, 2, 1, 1]] },
  { rep := [-1, -1, -2, -3, -3, -2, -1, 0], fc := [1],
    f := [-1, 0, -1, 0, 0, 0, 0], h := [-1, -1, 0, 0, -1, -1], d := 1,
    q := [0, 1],
    orbit := [[-1, -1, -2, -3, -3, -2, -1, 0], [0, -1, -1, -2, -2, -2, -1, 0],
       [0, -1, 0, -1, -1, -1, -1, 0], [0, -1, 0, 0, 0, 0, 0, 0], [-1, -1, -1, -1, 0, 0, 0, 0],
       [-1, -1, -2, -2, -1, 0, 0, 0], [-1, -1, -2, -3, -2, -1, 0, 0], [1, 1, 2, 3, 3, 2, 1, 0],
       [0, 1, 1, 2, 2, 2, 1, 0], [0, 1, 0, 1, 1, 1, 1, 0], [0, 1, 0, 0, 0, 0, 0, 0],
       [1, 1, 1, 1, 0, 0, 0, 0], [1, 1, 2, 2, 1, 0, 0, 0], [1, 1, 2, 3, 2, 1, 0, 0]] },
  { rep := [-1, -1, -2, -3, -2, -2, -2, -1], fc := [-1],
    f := [0, 0, 0, 1, -1, 1, 0], h := [0, 1, 2, 2, 2, 1], d := 1,
    q := [-1, 1, 0, 0, 1],
    orbit := [[-1, -1, -2, -3, -2, -2, -2, -1], [0, -1, -1, -2, -2, -1, -1, -1],
       [-1, -1, -1, -2, -2, -2, -1, -1], [-1, -1, -2, -2, -2, -2, -2, -1],
       [0, -1, -1, -2, -1, -1, -1, -1], [-1, -1, -1, -2, -2, -1, -1, -1],
       [-1, -1, -2, -2, -2, -2, -1, -1], [1, 1, 2, 3, 2, 2, 2, 1], [0, 1, 1, 2, 2, 1, 1, 1],
       [1, 1, 1, 2, 2, 2, 1, 1], [1, 1, 2, 2, 2, 2, 2, 1], [0, 1, 1, 2, 1, 1, 1, 1],
       [1, 1, 1, 2, 2, 1, 1, 1], [1, 1, 2, 2, 2, 2, 1, 1]] },
  { rep := [-1, -1, -2, -3, -2, -2, -1, 0], fc := [1],
    f := [0, -1, 0, 0, -1, 1, -1], h := [0, 1, 2, 1, 1, 1], d := 2,
    q := [-2, 2, -1, -1, 1, -1],
    orbit := [[-1, -1, -2, -3, -2, -2, -1, 0], [0, -1, -1, -2, -2, -1, -1, 0],
       [0, -1, 0, -1, -1, -1, 0, 0], [-1, -1, -1, -1, -1, -1, -1, 0], [0, -1, -1, -1, 0, 0, 0, 0],
       [-1, -1, -1, -2, -1, 0, 0, 0], [-1, -1, -2, -2, -2, -1, 0, 0], [1, 1, 2, 3, 2, 2, 1, 0],
       [0, 1, 1, 2, 2, 1, 1, 0], [0, 1, 0, 1, 1, 1, 0, 0], [1, 1, 1, 1, 1, 1, 1, 0],
       [0, 1, 1, 1, 0, 0, 0, 0], [1, 1, 1, 2, 1, 0, 0, 0], [1, 1, 2, 2, 2, 1, 0, 0]] },
  { rep := [-1, -1, -2, -3, -2, -1, -1, 0], fc := [1],
    f := [-1, 0, -1, 1, -1, 0, 0], h := [0, 1, 1, 1, 2, 1], d := 2,
    q := [-2, 1, 0, -1],
    orbit := [[-1, -1, -2, -3, -2, -1, -1, 0], [0, -1, -1, -2, -2, -1, 0, 0],
       [-1, -1, -1, -2, -2, -2, -1, 0], [0, -1, -1, -1, -1, -1, -1, 0], [0, -1, 0, -1, 0, 0, 0, 0],
       [-1, -1, -1, -1, -1, 0, 0, 0], [-1, -1, -2, -2, -1, -1, 0, 0], [1, 1, 2, 3, 2, 1, 1, 0],
       [0, 1, 1, 2, 2, 1, 0, 0], [1, 1, 1, 2, 2, 2, 1, 0], [0, 1, 1, 1, 1, 1, 1, 0],
       [0, 1, 0, 1, 0, 0, 0, 0], [1, 1, 1, 1, 1, 0, 0, 0], [1, 1, 2, 2, 1, 1, 0, 0]] },
  { rep := [-1, -1, -2, -2, -2, -2, -1, 0], fc := [1],
    f := [-1, 0, 0, -1, 0, 0, 0], h := [0, 1, 1, 1, 0, 0], d := 1,
    q := [-1],
    orbit := [[-1, -1, -2, -2, -2, -2, -1, 0], [0, -1, -1, -2, -1, -1, -1, 0],
       [0, -1, 0, -1, -1, 0, 0, 0], [-1, -1, -1, -1, -1, -1, 0, 0], [-1, -1, -2, -2, -1, -1, -1, 0],
       [0, -1, -1, -2, -1, 0, 0, 0], [-1, -1, -1, -2, -2, -1, 0, 0], [1, 1, 2, 2, 2, 2, 1, 0],
       [0, 1, 1, 2, 1, 1, 1, 0], [0, 1, 0, 1, 1, 0, 0, 0], [1, 1, 1, 1, 1, 1, 0, 0],
       [1, 1, 2, 2, 1, 1, 1, 0], [0, 1, 1, 2, 1, 0, 0, 0], [1, 1, 1, 2, 2, 1, 0, 0]] },
  { rep := [-1, -1, -2, -2, -2, -1, -1, 0], fc := [1],
    f := [-2, 1, -1, 0, 0, -1, 1], h := [-1, 0, 1, 1, 1, 1], d := 1,
    q := [1, -2, 0, 0, -1, 1],
    orbit := [[-1, -1, -2, -2, -2, -1, -1, 0], [0, -1, -1, -2, -1, -1, 0, 0],
       [-1, -1, -1, -2, -2, -1, -1, 0], [0, -1, -1, -1, -1, -1, 0, 0],
       [-1, -1, -1, -2, -1, -1, -1, 0], [0, -1, -1, -1, -1, 0, 0, 0],
       [-1, -1, -1, -2, -1, -1, 0, 0], [1, 1, 2, 2, 2, 1, 1, 0], [0, 1, 1, 2, 1, 1, 0, 0],
       [1, 1, 1, 2, 2, 1, 1, 0], [0, 1, 1, 1, 1, 1, 0, 0], [1, 1, 1, 2, 1, 1, 1, 0],
       [0, 1, 1, 1, 1, 0, 0, 0], [1, 1, 1, 2, 1, 1, 0, 0]] },
  { rep := [-1, 0, -1, -1, -1, -1, -1, -1], fc := [-2],
    f := [0, 1, 0, 1, 0, 1, 0], h := [-1, -1, 0, 0, 0, 0], d := 1,
    q := [-1],
    orbit := [[-1, 0, -1, -1, -1, -1, -1, -1], [0, 0, -1, -1, -1, -1, -1, -1],
       [0, 0, 0, -1, -1, -1, -1, -1], [0, 0, 0, 0, -1, -1, -1, -1], [0, 0, 0, 0, 0, -1, -1, -1],
       [0, 0, 0, 0, 0, 0, -1, -1], [0, 0, 0, 0, 0, 0, 0, -1], [1, 0, 1, 1, 1, 1, 1, 1],
       [0, 0, 1, 1, 1, 1, 1, 1], [0, 0, 0, 1, 1, 1, 1, 1], [0, 0, 0, 0, 1, 1, 1, 1],
       [0, 0, 0, 0, 0, 1, 1, 1], [0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 1]] },
  { rep := [-1, 0, -1, -1, -1, -1, -1, 0], fc := [0],
    f := [-1, 1, -1, 1, -1, 1, 0], h := [-2, 3, 8, 6, 4, 2], d := 7,
    q := [-5, 0, 2, 0, 2],
    orbit := [[-1, 0, -1, -1, -1, -1, -1, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0],
       [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0],
       [0, 0, 0, 0, 0, 0, 1, 0], [1, 0, 1, 1, 1, 1, 1, 0], [-1, 0, 0, 0, 0, 0, 0, 0],
       [0, 0, -1, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0],
       [0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, -1, 0]] },
  { rep := [-1, 0, -1, -1, -1, -1, 0, 0], fc := [0],
    f := [0, 0, 0, 0, 0, 1, -1], h := [-1, -2, 4, 3, 2, 1], d := 7,
    q := [-7, 7, 0, 0, 0, -1],
    orbit := [[-1, 0, -1, -1, -1, -1, 0, 0], [0, 0, -1, -1, -1, -1, -1, 0],
       [1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0, 0, 0],
       [0, 0, 0, 0, 1, 1, 0, 0], [0, 0, 0, 0, 0, 1, 1, 0], [1, 0, 1, 1, 1, 1, 0, 0],
       [0, 0, 1, 1, 1, 1, 1, 0], [-1, 0, -1, 0, 0, 0, 0, 0], [0, 0, -1, -1, 0, 0, 0, 0],
       [0, 0, 0, -1, -1, 0, 0, 0], [0, 0, 0, 0, -1, -1, 0, 0], [0, 0, 0, 0, 0, -1, -1, 0]] },
  { rep := [-1, 0, -1, -1, -1, 0, 0, 0], fc := [0],
    f := [-1, 1, -1, 1, 0, 0, 0], h := [-3, -6, -2, 2, -1, -4], d := 7,
    q := [-4, 7, -4],
    orbit := [[-1, 0, -1, -1, -1, 0, 0, 0], [0, 0, -1, -1, -1, -1, 0, 0],
       [0, 0, 0, -1, -1, -1, -1, 0], [1, 0, 1, 1, 0, 0, 0, 0], [0, 0, 1, 1, 1, 0, 0, 0],
       [0, 0, 0, 1, 1, 1, 0, 0], [0, 0, 0, 0, 1, 1, 1, 0], [1, 0, 1, 1, 1, 0, 0, 0],
       [0, 0, 1, 1, 1, 1, 0, 0], [0, 0, 0, 1, 1, 1, 1, 0], [-1, 0, -1, -1, 0, 0, 0, 0],
       [0, 0, -1, -1, -1, 0, 0, 0], [0, 0, 0, -1, -1, -1, 0, 0], [0, 0, 0, 0, -1, -1, -1, 0]] }]

@[expose] def e8O7Basis : List (List ℤ) :=
  lcols Tag.E8.rank (e8O7ThetaList :: lorbit Tag.E8.rank e8O7WList e8O7BetaList 7)

@[expose] def e8O7Conj : List (List ℤ) :=
  lmul Tag.E8.rank (lmul Tag.E8.rank e8O7BasisInv e8O7WList) e8O7Basis

@[expose] def e8O7ConjNeg : List (List ℤ) :=
  lmul Tag.E8.rank (lmul Tag.E8.rank e8O7BasisInv (lsmul Tag.E8.rank (-1) e8O7WList)) e8O7Basis

theorem e8O7W_eq : e8O7W = toMat Tag.E8.rank e8O7WList :=
  wordMat_eq_toMat .E8 _ (by decide +kernel)

theorem e8O7Theta_eq : e8O7Theta = toVec Tag.E8.rank e8O7ThetaList := by decide +kernel

theorem e8O7Beta_eq : e8O7Beta = toVec Tag.E8.rank e8O7BetaList := by decide +kernel

theorem e8O7Cols_eq' : e8O7Cols = fun j : Fin Tag.E8.rank => toVec Tag.E8.rank
    ((e8O7ThetaList :: lorbit Tag.E8.rank e8O7WList e8O7BetaList 7).getD j []) := by
  have h := cols_ite_eq (n := Tag.E8.rank) e8O7WList e8O7ThetaList e8O7BetaList 7
  rw [← e8O7Theta_eq, ← e8O7Beta_eq, ← e8O7W_eq] at h
  exact h

theorem e8O7Cols_eq :
    (Matrix.of fun i (j : Fin Tag.E8.rank) => e8O7Cols j i) = toMat Tag.E8.rank e8O7Basis := by
  rw [e8O7Basis, ← of_cols_eq_toMat, e8O7Cols_eq']

theorem e8O7Basis_mul_inv : lmul Tag.E8.rank e8O7Basis e8O7BasisInv = lid Tag.E8.rank := by
  decide +kernel

theorem e8O7Frame_eq :
    e8O7Frame = fun i : Fin Tag.E8.rank => toVec Tag.E8.rank (e8O7FrameList.getD i []) := by
  decide +kernel

theorem charpoly_one_by_one (c : ℤ) : (toMat 1 [[c]]).charpoly = X - C c := by
  have h : toMat 1 [[c]] = Matrix.diagonal fun _ => c := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  rw [h, Matrix.charpoly_diagonal, Fin.prod_univ_one]

theorem e8O7Conj_blocks :
    lowerLeftZero 1 7 e8O7Conj = true ∧ ltopLeft 1 e8O7Conj = [[1]] ∧
      lbotRight 1 7 e8O7Conj = [[0, 0, 0, 0, 0, 0, 1], [1, 0, 0, 0, 0, 0, 0],
        [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0],
        [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0]] := by
  decide +kernel

theorem e8O7ConjNeg_blocks :
    lowerLeftZero 1 7 e8O7ConjNeg = true ∧ ltopLeft 1 e8O7ConjNeg = [[-1]] ∧
      lbotRight 1 7 e8O7ConjNeg = [[0, 0, 0, 0, 0, 0, -1], [-1, 0, 0, 0, 0, 0, 0],
        [0, -1, 0, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0],
        [0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, -1, 0]] := by
  decide +kernel

theorem charpoly_e8O7W : e8O7W.charpoly = (X - 1) * (X ^ 7 - 1) := by
  have hc : (toMat Tag.E8.rank e8O7WList).charpoly = (toMat Tag.E8.rank e8O7Conj).charpoly := by
    rw [charpoly_eq_of_conj (B := toMat Tag.E8.rank e8O7Basis)
      (B' := toMat Tag.E8.rank e8O7BasisInv)
      (by rw [← toMat_lmul, e8O7Basis_mul_inv, toMat_lid]), e8O7Conj, toMat_lmul, toMat_lmul]
  obtain ⟨h₁, h₂, h₃⟩ := e8O7Conj_blocks
  have hb := charpoly_eq_mul_of_blocks (k := 1) (m := 7) e8O7Conj h₁
  rw [h₂, h₃, charpoly_one_by_one, map_one] at hb
  rw [e8O7W_eq, hc]
  refine Eq.trans (hb : (toMat Tag.E8.rank e8O7Conj).charpoly = _) (congrArg _ ?_)
  exact charpoly_eq_of_lists (cs := [-1, 0, 0, 0, 0, 0, 0, 1]) (by monicity!) (by compute_degree!)
    (by simp [polyOfList]; ring) (by decide +kernel) [1, 0, 0, 0, 0, 0, 0]
    (by rw [orbitMat_eq_toMat]; exact isUnit_det_of_lmul_eq_lid (N := lid 7) (by decide +kernel))

theorem charpoly_neg_e8O7W : (-e8O7W).charpoly = (X + 1) * (X ^ 7 + 1) := by
  have hc : (toMat Tag.E8.rank (lsmul Tag.E8.rank (-1) e8O7WList)).charpoly =
      (toMat Tag.E8.rank e8O7ConjNeg).charpoly := by
    rw [charpoly_eq_of_conj (B := toMat Tag.E8.rank e8O7Basis)
      (B' := toMat Tag.E8.rank e8O7BasisInv)
      (by rw [← toMat_lmul, e8O7Basis_mul_inv, toMat_lid]), e8O7ConjNeg, toMat_lmul, toMat_lmul]
  obtain ⟨h₁, h₂, h₃⟩ := e8O7ConjNeg_blocks
  have hb := charpoly_eq_mul_of_blocks (k := 1) (m := 7) e8O7ConjNeg h₁
  rw [h₂, h₃, charpoly_one_by_one, show (C (-1 : ℤ)) = -1 by simp, sub_neg_eq_add] at hb
  rw [e8O7W_eq, ← toMat_lsmul_neg_one, hc]
  refine Eq.trans (hb : (toMat Tag.E8.rank e8O7ConjNeg).charpoly = _) (congrArg _ ?_)
  exact charpoly_eq_of_lists (cs := [1, 0, 0, 0, 0, 0, 0, 1]) (by monicity!) (by compute_degree!)
    (by simp [polyOfList]; ring) (by decide +kernel) [1, 0, 0, 0, 0, 0, 0]
    (by
      rw [orbitMat_eq_toMat]
      exact isUnit_det_of_lmul_eq_lid (N := lcols 7 (lorbit 7 [[0, 0, 0, 0, 0, 0, -1],
        [-1, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0],
        [0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, -1, 0]]
          [1, 0, 0, 0, 0, 0, 0] 7)) (by decide +kernel))

theorem e8O7_det_basis : (toMat Tag.E8.rank e8O7Basis).det = 1 := by
  rw [det_toMat_eq_of_colAdds _ e8O7BasisOps (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem e8O7_root_kernel (p : ℕ) [Fact p.Prime] (hp7 : 7 < p) (a : ZMod p)
    (ha : a ^ 6 + a ^ 5 + a ^ 4 + a ^ 3 + a ^ 2 + a + 1 = 0) (z : Fin Tag.E8.rank → ZMod p)
    (hz0 : z ≠ 0)
    (hz : (e8O7W.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = a • z) :
    {α | IsRoot .E8 α ∧ pair α z = 0} = {e8O7Theta, -e8O7Theta} := by
  rw [e8O7W_eq] at hz
  have hΦ : peval [1, 1, 1, 1, 1, 1, 1] a = 0 := by
    simp only [peval_cons, peval_nil, Int.cast_one]
    linear_combination ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    norm_num at ha
  have ha1 : a ≠ 1 := by
    rintro rfl
    have h7 : ((7 : ℤ) : ZMod p) ≠ 0 := intCast_zmod_ne_zero (by norm_num) (by exact_mod_cast hp7)
    apply h7
    push_cast
    linear_combination ha
  have hθ : pair (toVec Tag.E8.rank e8O7ThetaList) z = 0 :=
    pair_eq_zero_of_fixed hz ha1 (by rw [← toVec_lmulVec]; exact congrArg _ (by decide +kernel))
  have hβ : pair (toVec Tag.E8.rank e8O7BetaList) z ≠ 0 := by
    intro h0
    apply hz0
    refine eq_zero_of_pair_cols_eq_zero (B := toMat Tag.E8.rank e8O7Basis)
      (by rw [e8O7_det_basis]; exact isUnit_one) fun j => ?_
    have hcol : (fun i => toMat Tag.E8.rank e8O7Basis i j) = toVec Tag.E8.rank ((e8O7ThetaList ::
        lorbit Tag.E8.rank e8O7WList e8O7BetaList 7).getD j []) := by
      rw [← e8O7Cols_eq]
      exact congrFun e8O7Cols_eq' j
    rw [hcol, getD_cons_eq_ite]
    have hj : (j : ℕ) < 8 := j.isLt
    split_ifs with h
    · exact hθ
    · rw [toVec_lorbit_getD (by omega), pair_pow_mulVec hz, h0, mul_zero]
  have hd : ∀ r ∈ e8O7Rows, 0 < r.d ∧ r.d ≤ 7 := by decide +kernel
  have hker := rootKernel_eq_of_rows (τ := .E8) (F := [e8O7ThetaList]) (β := e8O7BetaList)
    (Φ := [1, 1, 1, 1, 1, 1, 1]) (m := 7) (signed := true) e8O7Rows
    [e8O7ThetaList, vneg Tag.E8.rank e8O7ThetaList] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hz ha0 hΦ (by simpa using hθ) hβ
    (fun r hr => intCast_zmod_ne_zero (hd r hr).1 (by
      have h2 : (7 : ℤ) < p := by exact_mod_cast hp7
      have := (hd r hr).2
      omega))
    (by
      intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact hθ
      · rw [toVec_vneg, pair_neg, hθ]
        exact neg_zero)
  refine hker.trans ?_
  ext α
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left, Set.mem_insert_iff, Set.mem_singleton_iff, e8O7Theta_eq, toVec_vneg]

theorem E8_order_seven_lattice_exact_A1_root_kernel_and_negative_frame :
    IsRoot .E8 e8O7Theta ∧ IsRoot .E8 e8O7Beta ∧ orderOf e8O7W = 7 ∧
    e8O7W *ᵥ e8O7Theta = e8O7Theta ∧ Tag.E8.cartan *ᵥ e8O7Theta = Pi.single 7 1 ∧
    (LinearIndependent ℤ e8O7Cols ∧ Submodule.span ℤ (Set.range e8O7Cols) = ⊤) ∧
    (Matrix.of fun i (j : Fin Tag.E8.rank) => e8O7Cols j i).det = 1 ∧
    e8O7W.charpoly = (X - 1) * (X ^ 7 - 1) ∧ (-e8O7W).charpoly = (X + 1) * (X ^ 7 + 1) ∧
    (∀ p : ℕ, p.Prime → 7 < p → ∀ a : ZMod p,
      a ^ 6 + a ^ 5 + a ^ 4 + a ^ 3 + a ^ 2 + a + 1 = 0 →
      ∀ z : Fin Tag.E8.rank → ZMod p, z ≠ 0 → (e8O7W.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = a • z →
        {α | IsRoot .E8 α ∧ pair α z = 0} = {e8O7Theta, -e8O7Theta}) ∧
    (∀ i, IsRoot .E8 (e8O7Frame i)) ∧ gramMat .E8 e8O7Frame = 2 ∧
    (List.ofFn fun i => rootReflMat .E8 (e8O7Frame i)).prod = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, charpoly_e8O7W, charpoly_neg_e8O7W,
    fun p hp hp7 a ha z hz0 hz => @e8O7_root_kernel p ⟨hp⟩ hp7 a ha z hz0 hz, ?_, ?_, ?_⟩
  · rw [e8O7Theta_eq]
    exact isRoot_toVec (by decide +kernel)
  · rw [e8O7Beta_eq]
    exact isRoot_toVec (by decide +kernel)
  · rw [e8O7W_eq]
    exact orderOf_toMat_eq (by norm_num) (by decide +kernel) (by decide +kernel)
  · rw [e8O7W_eq, e8O7Theta_eq, ← toVec_lmulVec]
    exact congrArg _ (by decide +kernel)
  · have h : Tag.E8.cartan *ᵥ e8O7Theta =
        toVec Tag.E8.rank (lmulVec Tag.E8.rank (cartanList .E8) e8O7ThetaList) := by
      rw [toVec_lmulVec, ← e8O7Theta_eq, toMat_cartanList]
    rw [h]
    decide +kernel
  · rw [Module.Basis.is_basis_iff_det (Pi.basisFun ℤ (Fin Tag.E8.rank)), Module.Basis.det_apply]
    have h : (Pi.basisFun ℤ (Fin Tag.E8.rank)).toMatrix e8O7Cols =
        Matrix.of fun i (j : Fin Tag.E8.rank) => e8O7Cols j i := rfl
    rw [h, e8O7Cols_eq, e8O7_det_basis]
    exact isUnit_one
  · rw [e8O7Cols_eq, e8O7_det_basis]
  · have hmem : ∀ l ∈ e8O7FrameList, l ∈ Tag.E8.artifactRoots := by decide +kernel
    intro i
    rw [e8O7Frame_eq]
    have hlen : ∀ i : Fin Tag.E8.rank, e8O7FrameList.getD i [] ∈ e8O7FrameList := by
      decide +kernel
    exact isRoot_toVec (hmem _ (hlen i))
  · have h := toMat_lgram .E8 (toMat_cartanList .E8) Tag.E8.rank e8O7FrameList
    rw [e8O7Frame_eq]
    refine h.symm.trans ?_
    decide +kernel
  · rw [e8O7Frame_eq]
    rw [prod_rootReflMat_eq .E8 (k := Tag.E8.rank) e8O7FrameList, prod_map_toMat, neg_one_eq_toMat]
    exact congrArg _ (by decide +kernel)

end CFSG.RankThree.Lattice
