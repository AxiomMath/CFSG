module

public import CFSG.RankThree.Asc83Table.M22Data
public import CFSG.Assembly.Defs

public section

namespace CFSG.RankThree.PartTwo.KFacts.KP4

open Equiv
open CFSG.RankThree.Asc83Table.M22 (x y)

@[expose] def line : Fin 4 → Perm (Fin 22) := ![x, y, x * y, x * y ^ 2]

@[expose] def lineTab : Fin 4 → Array ℕ :=
  ![#[0, 6, 19, 1, 7, 18, 3, 9, 21, 4, 8, 5, 2, 17, 14, 15, 13, 16, 11, 12, 20, 10],
    #[0, 7, 12, 4, 17, 18, 9, 16, 8, 13, 10, 5, 19, 6, 15, 20, 1, 3, 11, 2, 14, 21],
    #[0, 9, 2, 7, 16, 11, 4, 13, 21, 17, 8, 18, 12, 3, 15, 20, 6, 1, 5, 19, 14, 10],
    #[0, 13, 12, 16, 1, 5, 17, 6, 21, 3, 8, 11, 19, 4, 20, 14, 9, 7, 18, 2, 15, 10]]

@[expose] def ofTab (t : Array ℕ) (p : Fin 22) : Fin 22 :=
  ⟨t[p.val]! % 22, Nat.mod_lt _ (by norm_num)⟩

@[expose] def vA : Fin 4 → Perm (Fin 22) :=
  ![List.formPerm [0, 15] * List.formPerm [1, 10] * List.formPerm [3, 21] * List.formPerm [4, 17] *
      List.formPerm [6, 8] * List.formPerm [7, 16] * List.formPerm [9, 13] *
      List.formPerm [14, 20],
    List.formPerm [0, 21] * List.formPerm [1, 6] * List.formPerm [3, 15] * List.formPerm [4, 20] *
      List.formPerm [7, 9] * List.formPerm [8, 10] * List.formPerm [13, 16] *
      List.formPerm [14, 17],
    List.formPerm [0, 12] * List.formPerm [1, 11] * List.formPerm [2, 19] * List.formPerm [3, 16] *
      List.formPerm [4, 13] * List.formPerm [5, 17] * List.formPerm [6, 7] *
      List.formPerm [9, 18],
    List.formPerm [0, 11] * List.formPerm [1, 12] * List.formPerm [2, 4] * List.formPerm [3, 7] *
      List.formPerm [5, 18] * List.formPerm [6, 16] * List.formPerm [9, 17] *
      List.formPerm [13, 19]]

@[expose] def vB : Fin 4 → Perm (Fin 22) :=
  ![List.formPerm [0, 14] * List.formPerm [1, 7] * List.formPerm [3, 4] * List.formPerm [6, 9] *
      List.formPerm [8, 13] * List.formPerm [10, 16] * List.formPerm [15, 20] *
      List.formPerm [17, 21],
    List.formPerm [0, 8] * List.formPerm [1, 3] * List.formPerm [4, 7] * List.formPerm [6, 15] *
      List.formPerm [9, 20] * List.formPerm [10, 21] * List.formPerm [13, 14] *
      List.formPerm [16, 17],
    List.formPerm [0, 19] * List.formPerm [1, 4] * List.formPerm [2, 12] * List.formPerm [3, 18] *
      List.formPerm [5, 7] * List.formPerm [6, 17] * List.formPerm [9, 16] *
      List.formPerm [11, 13],
    List.formPerm [0, 18] * List.formPerm [1, 17] * List.formPerm [2, 16] * List.formPerm [3, 19] *
      List.formPerm [4, 6] * List.formPerm [5, 11] * List.formPerm [7, 13] *
      List.formPerm [9, 12]]

@[expose] def tw : Fin 4 → Perm (Fin 22) := ![y, x, x, x]

@[expose] def vAWord : Fin 4 → List (ℕ × ℤ) :=
  ![[(0, 1), (1, 1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, -1), (0, 1),
      (1, 1), (0, 1), (1, -1), (0, 1)],
    [(1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, -1), (0, 1), (1, 1),
      (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2)],
    [(1, 1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 2),
      (0, 1), (1, -1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, -1)],
    [(0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, -1), (0, 1), (1, 2), (0, 1),
      (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2), (0, 1), (1, -1), (0, 1), (1, -1)]]

@[expose] def hexOne : Finset (Fin 22) := {2, 5, 11, 12, 18, 19}

@[expose] def hexTwo : Finset (Fin 22) := {8, 10, 14, 15, 20, 21}

@[expose] def tri : Fin 4 → Finset (Fin 22) :=
  ![{14, 15, 20}, {8, 10, 21}, {2, 12, 19}, {5, 11, 18}]

@[expose] def pairFst : Fin 4 → Fin 4 := ![0, 0, 1, 1]

@[expose] def pairSnd : Fin 4 → Fin 4 := ![2, 3, 2, 3]

@[expose] def hep : Fin 4 → Finset (Fin 22) :=
  ![{0, 2, 12, 14, 15, 19, 20}, {0, 5, 11, 14, 15, 18, 20}, {0, 2, 8, 10, 12, 19, 21},
    {0, 5, 8, 10, 11, 18, 21}]

end CFSG.RankThree.PartTwo.KFacts.KP4
