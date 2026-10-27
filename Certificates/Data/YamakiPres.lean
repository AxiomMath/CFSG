module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Logic.Equiv.Fin.Basic

public section

namespace CFSG.ClassicalInvolution.Solomon73.Yamaki

open Matrix

@[expose] def posW {m : ℕ} (l : List (Fin m)) : List (Fin m × Bool) := l.map fun i => (i, true)

@[expose] def invW {m : ℕ} (w : List (Fin m × Bool)) : List (Fin m × Bool) :=
  (w.map fun l => (l.1, !l.2)).reverse

@[expose] def relW {m : ℕ} (v w : List (Fin m × Bool)) : List (Fin m × Bool) := v ++ invW w

@[expose] def commW {m : ℕ} (x y : Fin m) : List (Fin m × Bool) :=
  [(x, false), (y, false), (x, true), (y, true)]

@[expose] def rels31 (_ : Unit := ()) : List (List (Fin 12 × Bool)) :=
  ([0, 1, 2, 3, 4, 5, 6, 7, 8] : List (Fin 12)).map (fun i => posW [i, i]) ++
  ([3, 4, 5, 6, 7, 8] : List (Fin 12)).flatMap (fun i =>
    (([3, 4, 5, 6, 7, 8] : List (Fin 12)).filter fun j => i < j).map (commW i)) ++
  [relW (posW [0, 2, 0, 2]) (posW [1])] ++
  ([3, 4, 5, 8] : List (Fin 12)).map (commW 0) ++
  [relW (posW [0, 6, 0]) (posW [3, 6]), relW (posW [0, 7, 0]) (posW [4, 5, 7])] ++
  ([4, 5, 6, 7] : List (Fin 12)).map (commW 2) ++
  [relW (posW [2, 3, 2]) (posW [3, 4]), relW (posW [2, 8, 2]) (posW [6, 7, 8])]

@[expose] def rels33 (_ : Unit := ()) : List (List (Fin 12 × Bool)) :=
  [posW [9, 9], posW [10, 10], posW [11, 11], posW [9, 10, 9, 10, 9, 10],
    posW [10, 11, 10, 11, 10, 11, 10, 11], posW [9, 11, 9, 11]]

@[expose] def rels35 (_ : Unit := ()) : List (List (Fin 12 × Bool)) :=
  [posW [9, 0, 9, 0, 9, 0], posW [10, 2, 10, 2, 10, 2], posW [11, 8, 11, 8, 11, 8]]

@[expose] def actW (w : Fin 12) (l : List (Fin 12 × Fin 12)) : List (List (Fin 12 × Bool)) :=
  l.map fun p => relW (posW [w, p.1, w]) (posW [p.2])

@[expose] def rels36 (_ : Unit := ()) : List (List (Fin 12 × Bool)) :=
  actW 9 [(1, 2), (2, 1), (3, 6), (4, 4), (5, 7), (6, 3), (7, 5), (8, 8)] ++
  actW 10 [(0, 1), (1, 0), (3, 4), (4, 3), (5, 5), (6, 6), (7, 8), (8, 7)] ++
  actW 11 [(0, 0), (1, 3), (2, 6), (3, 1), (4, 4), (5, 5), (6, 2), (7, 7)]

@[expose] def yamakiRels (_ : Unit := ()) : List (List (Fin 12 × Bool)) :=
  rels31 () ++ rels33 () ++ rels35 () ++ rels36 ()

@[expose] def yamakiMat6 : Fin 12 → Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![!![1, 0, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0; 1, 1, 0, 0, 0, 0;
      0, 0, 1, 1, 1, 1; 0, 0, 1, 0, 0, 1; 1, 1, 0, 0, 1, 0],
    !![1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1; 0, 1, 0, 0, 1, 0],
    !![1, 1, 0, 0, 1, 1; 1, 1, 0, 1, 0, 0; 1, 0, 1, 1, 0, 0;
      0, 1, 0, 1, 1, 1; 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1],
    !![1, 0, 1, 0, 1, 1; 1, 0, 0, 1, 0, 1; 1, 1, 0, 1, 1, 0;
      0, 0, 1, 1, 1, 1; 0, 0, 1, 0, 0, 1; 1, 1, 0, 1, 0, 0],
    !![1, 0, 1, 0, 1, 1; 1, 1, 0, 1, 0, 0; 1, 0, 1, 1, 0, 0;
      0, 0, 1, 1, 1, 1; 0, 0, 0, 0, 1, 0; 1, 0, 0, 1, 0, 1],
    !![1, 0, 0, 0, 0, 0; 0, 1, 1, 0, 1, 1; 0, 0, 0, 0, 1, 1;
      0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 1, 0],
    !![1, 1, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0; 1, 0, 1, 1, 0, 0;
      0, 1, 0, 1, 0, 1; 1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 0, 1],
    !![0, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0;
      1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1],
    !![0, 1, 0, 1, 0, 1; 0, 1, 0, 0, 0, 0; 1, 1, 1, 1, 0, 1;
      1, 1, 0, 0, 0, 1; 1, 1, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1],
    !![0, 1, 0, 0, 1, 0; 0, 0, 1, 1, 0, 1; 1, 1, 1, 0, 1, 0;
      0, 1, 1, 0, 0, 1; 1, 0, 1, 1, 0, 1; 1, 1, 0, 0, 1, 1],
    !![1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1; 1, 1, 0, 0, 1, 0;
      0, 1, 0, 1, 0, 1; 1, 0, 1, 0, 0, 1; 0, 1, 0, 0, 0, 0],
    !![0, 0, 0, 1, 1, 0; 1, 1, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0;
      1, 0, 0, 0, 1, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]]

@[expose] def yamakiMat (i : Fin 12) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  (yamakiMat6 i).submatrix finSumFinEquiv finSumFinEquiv

@[expose] def vecOf (n : ℕ) : Fin 3 ⊕ Fin 3 → ZMod 2 :=
  fun a => if n.testBit (finSumFinEquiv a).val then 1 else 0

@[expose] def wordMat {m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Fin m → Matrix ι ι (ZMod 2)) (w : List (Fin m × Bool)) : Matrix ι ι (ZMod 2) :=
  (w.map fun l => M l.1).prod

@[expose] def halfOK {m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Fin m → Matrix ι ι (ZMod 2)) (w : List (Fin m × Bool)) : Bool :=
  decide (wordMat M (w.take (w.length / 2)) = wordMat M (w.drop (w.length / 2)).reverse)

@[expose] def spInvolCheck (_ : Unit := ()) : Bool :=
  (List.finRange 12).all fun i => decide (yamakiMat i * yamakiMat i = 1)

@[expose] def spSympCheck (_ : Unit := ()) : Bool :=
  (List.finRange 12).all fun i => decide ((yamakiMat i)ᵀ * fromBlocks 0 1 (-1) 0 * yamakiMat i =
    fromBlocks 0 1 (-1) 0)

@[expose] def spRelCheck (_ : Unit := ()) : Bool := (yamakiRels ()).all (halfOK yamakiMat)

@[expose] def spTransvCheck (_ : Unit := ()) : Bool :=
  decide (∀ y : Fin 3 ⊕ Fin 3 → ZMod 2,
    yamakiMat 7 *ᵥ y = y + (y ⬝ᵥ (fromBlocks 0 1 (-1) 0 *ᵥ vecOf 9)) • vecOf 9)

@[expose] def yamakiOrbit : List (ℕ × ℕ × Fin 12) :=
  [(47, 9, 0), (38, 9, 9), (29, 9, 10), (59, 47, 10), (20, 29, 2), (22, 29, 11), (50, 59, 2),
    (48, 59, 11), (31, 20, 11), (11, 22, 8), (56, 22, 10), (57, 50, 11), (45, 48, 8), (30, 48, 10),
    (2, 31, 8), (37, 31, 10), (49, 11, 10), (46, 56, 2), (13, 56, 9), (36, 57, 8), (3, 57, 10),
    (23, 45, 10), (8, 30, 2), (4, 30, 9), (44, 2, 10), (58, 37, 2), (16, 37, 9), (39, 49, 2),
    (43, 49, 9), (51, 46, 8), (27, 46, 9), (53, 13, 0), (10, 36, 10), (28, 3, 2), (25, 3, 9),
    (1, 23, 2), (34, 23, 9), (21, 8, 8), (18, 8, 9), (26, 4, 0), (54, 44, 9), (32, 58, 9),
    (40, 16, 0), (61, 39, 9), (19, 43, 0), (6, 51, 9), (35, 27, 0), (60, 53, 7), (63, 10, 9),
    (41, 28, 9), (7, 25, 0), (52, 1, 9), (15, 21, 9), (12, 18, 0), (14, 54, 0), (24, 32, 0),
    (55, 40, 2), (33, 40, 7), (5, 61, 0), (62, 6, 0), (42, 35, 7), (17, 15, 0)]

@[expose] def orbitOK : List ℕ → List (ℕ × ℕ × Fin 12) → Bool
  | _, [] => true
  | seen, (c, p, k) :: l =>
    seen.contains p && decide (yamakiMat k *ᵥ vecOf p = vecOf c) && orbitOK (c :: seen) l

@[expose] def spOrbitCheck (_ : Unit := ()) : Bool := orbitOK [9] yamakiOrbit

@[expose] def spCoverCheck (_ : Unit := ()) : Bool :=
  decide (∀ v : Fin 3 ⊕ Fin 3 → ZMod 2, v = 0 ∨ v = vecOf 9 ∨ ∃ e ∈ yamakiOrbit, vecOf e.1 = v)

@[expose] def gl32Rels (_ : Unit := ()) : List (List (Fin 4 × Bool)) :=
  [posW [0, 0], posW [1, 1], posW [2, 2], posW [3, 3], posW [0, 2, 0, 2, 0, 2],
    posW [1, 3, 1, 3, 1, 3], posW [0, 1, 0, 1, 0, 1], relW (posW [0, 3, 0]) (posW [2, 3, 2, 3]),
    relW (posW [1, 2, 1]) (posW [2, 3, 2, 3])]

@[expose] def gl32Mat : Fin 4 → Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  ![!![0, 1, 0; 1, 0, 0; 0, 0, 1], !![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 1, 0; 0, 1, 0; 0, 0, 1],
    !![1, 0, 0; 0, 1, 1; 0, 0, 1]]

@[expose] def gl32TransvWord : Fin 3 → Fin 3 → List (Fin 4) :=
  ![![[], [2], [0, 3, 0]], ![[0, 2, 0], [], [3]], ![[0, 1, 3, 1, 0], [1, 3, 1], []]]

@[expose] def glInvolCheck (_ : Unit := ()) : Bool :=
  (List.finRange 4).all fun i => decide (gl32Mat i * gl32Mat i = 1)

@[expose] def glRelCheck (_ : Unit := ()) : Bool := (gl32Rels ()).all (halfOK gl32Mat)

@[expose] def glTransvCheck (_ : Unit := ()) : Bool :=
  decide (∀ i j : Fin 3, i ≠ j → ((gl32TransvWord i j).map gl32Mat).prod = 1 + Matrix.single i j 1)

end CFSG.ClassicalInvolution.Solomon73.Yamaki
