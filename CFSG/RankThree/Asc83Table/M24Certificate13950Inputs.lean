module

public import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.RankThree.Asc83Table.M24

open CFSG.Blueprint CFSG.Sporadic.Mathieu Subgroup
open scoped commutatorElement

abbrev gens : List (Equiv.Perm (Fin 24)) := [m24gA, m24gB]

abbrev x : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 10, 12] * List.formPerm [1, 15, 7] * List.formPerm [5, 23, 8] *
    List.formPerm [6, 18, 16] * List.formPerm [11, 14, 17] * List.formPerm [13, 21, 19]

abbrev y : Equiv.Perm (Fin 24) :=
  List.formPerm [2, 19, 16] * List.formPerm [3, 9, 22] * List.formPerm [4, 13, 18] *
    List.formPerm [6, 20, 21] * List.formPerm [8, 11, 12] * List.formPerm [10, 17, 23]

abbrev g1R : Equiv.Perm (Fin 24) :=
  List.formPerm [2, 6, 19, 20, 16, 21] * List.formPerm [3, 22, 9] * List.formPerm [4, 18, 13] *
    List.formPerm [5, 14] * List.formPerm [7, 15] * List.formPerm [8, 10, 11, 17, 12, 23]

abbrev g1S : Equiv.Perm (Fin 24) :=
  List.formPerm [2, 20] * List.formPerm [3, 22] * List.formPerm [5, 14] * List.formPerm [6, 19] *
    List.formPerm [8, 11] * List.formPerm [13, 18] * List.formPerm [16, 21] * List.formPerm [17, 23]

abbrev g2R : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 23, 12, 5, 10, 8] * List.formPerm [1, 15, 7] * List.formPerm [3, 22] *
    List.formPerm [4, 20] * List.formPerm [6, 21, 16, 13, 18, 19] * List.formPerm [11, 14, 17]

abbrev g2S : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 5] * List.formPerm [4, 20] * List.formPerm [6, 18] * List.formPerm [7, 15] *
    List.formPerm [8, 10] * List.formPerm [11, 17] * List.formPerm [12, 23] * List.formPerm [13, 21]

abbrev g3R : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 19, 17, 20, 11, 16] * List.formPerm [1, 22, 15, 9, 7, 3] *
    List.formPerm [2, 8, 18, 14, 13, 23] * List.formPerm [4, 12, 6, 5, 21, 10]

abbrev g3S : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 19] * List.formPerm [1, 22] * List.formPerm [2, 8] * List.formPerm [3, 15] *
    List.formPerm [4, 12] * List.formPerm [5, 21] * List.formPerm [6, 10] * List.formPerm [7, 9] *
    List.formPerm [11, 20] * List.formPerm [13, 14] * List.formPerm [16, 17] *
    List.formPerm [18, 23]

abbrev g4R : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 2, 12, 18, 17, 19] * List.formPerm [1, 9, 7, 3, 15, 22] *
    List.formPerm [4, 11, 6, 23, 13, 14] * List.formPerm [5, 20, 8, 16, 10, 21]

abbrev g4S : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 2, 10, 6, 8, 19] * List.formPerm [1, 9, 15, 3, 7, 22] *
    List.formPerm [4, 17, 16, 12, 13, 14] * List.formPerm [5, 20, 23, 18, 11, 21]

abbrev x_c0 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 3, 15, 16, 13, 12, 9, 6, 8, 22, 1, 7, 21, 19, 10, 14, 2, 23, 20, 4, 17] *
    List.formPerm [5, 11, 18]

abbrev x_c1 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 23, 10, 22, 2, 6] * List.formPerm [1, 11, 15, 20] *
    List.formPerm [3, 18, 13, 14, 21, 16, 19, 4, 7, 5, 9, 12] * List.formPerm [8, 17]

abbrev x_c2 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 6, 3, 13, 17, 5, 18, 22, 12, 4, 7, 8, 14, 21, 20] * List.formPerm [1, 16, 19] *
    List.formPerm [9, 23, 11, 15, 10]

abbrev x_c3 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 1, 22, 13, 12, 7, 15, 21, 8, 6, 19, 14, 16, 17, 4, 11, 9, 10, 5, 18, 23, 2, 3]

abbrev y_c0 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 11] * List.formPerm [1, 15, 18, 17, 14, 6, 4, 19, 21, 5, 12, 2, 23, 10] *
    List.formPerm [3, 9, 13, 8, 7, 22, 20]

abbrev y_c1 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 15, 7, 11, 9, 18, 10, 14, 17, 23, 3, 6] *
    List.formPerm [1, 20, 4, 22, 21, 5, 13, 2, 16, 12, 8, 19]

abbrev y_c2 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 22, 19, 10, 1, 18, 3, 12, 23, 17, 2, 7, 5, 20, 15, 9, 14, 8, 6, 21, 13] *
    List.formPerm [4, 11, 16]

abbrev y_c3 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 2, 5] * List.formPerm [3, 12, 7] * List.formPerm [6, 16, 11] *
    List.formPerm [9, 20, 14] * List.formPerm [10, 15, 22] * List.formPerm [17, 21, 19]

abbrev g1R_c0 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 18, 4, 16, 8, 12, 21, 3, 5, 22, 6, 14] *
    List.formPerm [1, 17, 10, 15, 9, 19, 20, 23, 11, 13, 7, 2]

abbrev g1R_c1 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 21, 9, 10, 17, 14, 4, 12, 22, 18] *
    List.formPerm [1, 11, 19, 15, 6, 13, 20, 8, 23, 5] * List.formPerm [2, 16] *
    List.formPerm [3, 7]

abbrev g1R_c2 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 17, 20, 14, 7, 9] * List.formPerm [1, 16, 4, 18] *
    List.formPerm [2, 12, 13, 22, 19, 11, 5, 15, 6, 21, 3, 23] * List.formPerm [8, 10]

abbrev g1S_c0 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 8, 21, 5, 1, 9, 17, 13, 16, 15, 19] *
    List.formPerm [2, 18, 3, 11, 7, 14, 22, 10, 6, 12, 4]

abbrev g1S_c1 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 14, 22, 15, 13, 2, 20, 9, 17, 1, 3, 5, 11, 19, 10, 6, 21, 23, 7, 12, 18, 16, 8]

abbrev g1S_c2 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 11, 8, 1, 3] * List.formPerm [4, 7, 5, 23, 20] *
    List.formPerm [6, 22, 12, 10, 14] * List.formPerm [9, 17, 21, 15, 18]

abbrev g2R_c0 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 8, 9, 13, 22, 10, 7, 23, 3, 16, 18, 15, 20, 2, 12] *
    List.formPerm [1, 11, 4, 6, 5] * List.formPerm [14, 17, 21]

abbrev g2R_c1 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 2, 19, 23, 14, 10, 13, 12, 9, 21, 6, 7, 3, 4] *
    List.formPerm [1, 16, 18, 15, 5, 11, 17] * List.formPerm [20, 22]

abbrev g2R_c2 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 6, 11, 9, 8, 13, 1, 16, 12, 21, 7, 15, 14, 23] *
    List.formPerm [2, 22, 19, 3, 10, 4, 18] * List.formPerm [5, 20]

abbrev g2S_c0 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 19, 15, 7, 16, 1, 2] *
    List.formPerm [3, 4, 22, 17, 23, 8, 14, 6, 13, 10, 12, 20, 9, 18] * List.formPerm [11, 21]

abbrev g2S_c1 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 6, 17, 20, 4, 8, 19, 15, 14, 11, 7, 5, 3, 12] * List.formPerm [1, 21] *
    List.formPerm [2, 13, 16, 10, 23, 18, 22]

abbrev g2S_c2 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 22, 8, 5, 15, 12, 19, 16, 10, 20, 6] *
    List.formPerm [1, 17, 21, 14, 9, 3, 11, 4, 13, 23, 7]

abbrev g2S_c3 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 23, 19, 15, 12, 20, 8, 2, 17, 7, 22, 10, 16, 3, 13, 21, 6, 14, 11, 18, 5] *
    List.formPerm [1, 4, 9]

abbrev g3R_c0 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 11] * List.formPerm [1, 15, 18, 17, 14, 6, 4, 19, 21, 5, 12, 2, 23, 10] *
    List.formPerm [3, 9, 13, 8, 7, 22, 20]

abbrev g3R_c1 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 2, 21, 15, 4, 20] * List.formPerm [1, 22, 17, 19, 23, 11, 6, 13, 18, 9, 8, 3] *
    List.formPerm [5, 7, 10, 14] * List.formPerm [12, 16]

abbrev g3R_c2 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 15, 8, 21, 19, 13] * List.formPerm [1, 5, 17] * List.formPerm [2, 6] *
    List.formPerm [3, 7, 4, 14, 18, 22] * List.formPerm [10, 11, 12] * List.formPerm [16, 23]

abbrev g3S_c0 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 13, 8, 9, 22, 7, 10, 14, 20, 15, 11, 3, 2, 16, 19, 12, 21, 5, 17, 1, 18, 6, 23]

abbrev g3S_c1 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 16, 9, 4, 14, 3] * List.formPerm [1, 2, 15, 22, 19, 11] *
    List.formPerm [6, 21, 23] * List.formPerm [7, 20, 17] * List.formPerm [8, 12] *
    List.formPerm [13, 18]

abbrev g3S_c2 : Equiv.Perm (Fin 24) :=
  List.formPerm [1, 16, 5, 8, 14, 3, 7, 12, 9, 15, 19, 21, 6, 17] *
    List.formPerm [2, 18, 23, 11, 4, 22, 20] * List.formPerm [10, 13]

abbrev g4R_c0 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 3, 16, 21, 1, 19, 23, 18, 7, 10, 13, 15, 9, 11] *
    List.formPerm [2, 6, 4, 22, 17, 12, 5] * List.formPerm [8, 14]

abbrev g4R_c1 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 2] * List.formPerm [1, 23, 10, 18, 3, 15, 11, 22, 9, 7, 14, 17, 21, 5] *
    List.formPerm [4, 12, 13, 16, 19, 6, 8]

abbrev g4R_c2 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 21, 4, 22, 17, 5, 20, 7, 2, 14, 19, 15, 8, 18, 11] * List.formPerm [1, 3, 12] *
    List.formPerm [6, 16, 9, 10, 13]

abbrev g4S_c0 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 2, 12, 5, 19, 21, 18, 13, 15, 8, 7, 20, 22, 16, 10, 14, 9, 23, 4, 11, 3] *
    List.formPerm [1, 17, 6]

abbrev g4S_c1 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 18, 23, 15, 16, 13] * List.formPerm [1, 12, 6, 5, 19, 17] *
    List.formPerm [2, 10, 3, 22, 9, 8] * List.formPerm [4, 7, 11, 21, 20, 14]

abbrev g4S_c2 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 3, 4, 14, 18, 10, 20] * List.formPerm [1, 21, 12, 2, 13, 23, 16] *
    List.formPerm [5, 7, 9, 8, 11, 22, 17]

abbrev g4S_c3 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 2, 15, 5, 3, 7, 1, 10, 19, 18, 4, 22, 21, 16, 9, 23, 8, 6, 13, 12, 20, 11, 17]

end CFSG.RankThree.Asc83Table.M24
