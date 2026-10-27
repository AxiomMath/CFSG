module

public import CFSG.Sporadic.Schreier.CountSpec

public section

namespace CFSG.RankThree.Asc83Table.M22

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier

abbrev x : Equiv.Perm (Fin 22) :=
  List.formPerm [1, 6, 3] * List.formPerm [2, 19, 12] * List.formPerm [4, 7, 9] *
    List.formPerm [5, 18, 11] * List.formPerm [8, 21, 10] * List.formPerm [13, 17, 16]

abbrev y : Equiv.Perm (Fin 22) :=
  List.formPerm [1, 7, 16] * List.formPerm [2, 12, 19] * List.formPerm [3, 4, 17] *
    List.formPerm [5, 18, 11] * List.formPerm [6, 9, 13] * List.formPerm [14, 15, 20]

abbrev gI : Equiv.Perm (Fin 22) :=
  List.formPerm [2, 5, 19, 18] * List.formPerm [3, 16, 6, 7] * List.formPerm [4, 17, 13, 9] *
    List.formPerm [8, 20, 21, 14] * List.formPerm [10, 15] * List.formPerm [11, 12]

abbrev gJ : Equiv.Perm (Fin 22) :=
  List.formPerm [2, 20, 19, 14] * List.formPerm [3, 17, 6, 9] * List.formPerm [4, 7, 13, 16] *
    List.formPerm [5, 8, 18, 21] * List.formPerm [10, 11] * List.formPerm [12, 15]

abbrev w (k : ℕ) : Equiv.Perm (Fin 22) := x ^ (k / 3) * y ^ (k % 3)

@[expose] def xT : Table := toTable x

@[expose] def yT : Table := toTable y

@[expose] def wT : Array Table := Array.ofFn (n := 9) fun k => toTable (w k.val)

@[expose] def m22Q8 : List (ℕ × ℕ) :=
  [(2, 3), (1, 6), (3, 1), (4, 5), (5, 8), (6, 2), (7, 4), (8, 7)]

@[expose] def m22Bad (T : Table) : Bool :=
  ap T 0 == 0 &&
    (List.range 9).any fun k => compT 22 T xT == compT 22 wT[k]! T &&
      (List.range 9).any fun l => compT 22 T yT == compT 22 wT[l]! T && !m22Q8.contains (k, l)

end CFSG.RankThree.Asc83Table.M22
