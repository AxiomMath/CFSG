module

public import Certificates.Data.S5RowsU33
public import Certificates.Data.S7SocQ8

public section

namespace Certificates.S7SocU33

open CFSG.GH74.KGroups Certificates.S5Rows Certificates.S7SocQ8 Certificates.S5RowsU33

@[expose] def u33Q0i : Equiv.Perm (Fin 28) :=
  List.formPerm [0, 11, 15, 16] * List.formPerm [1, 25, 5, 24] * List.formPerm [2, 17, 10, 9] *
    List.formPerm [3, 19] * List.formPerm [4, 14, 23, 13] * List.formPerm [6, 21, 7, 22] *
    List.formPerm [8, 27] * List.formPerm [12, 26, 20, 18]

@[expose] def u33Q0j : Equiv.Perm (Fin 28) :=
  List.formPerm [0, 23, 15, 4] * List.formPerm [1, 21, 5, 22] * List.formPerm [2, 18, 10, 26] *
    List.formPerm [3, 8] * List.formPerm [6, 24, 7, 25] * List.formPerm [9, 12, 17, 20] *
    List.formPerm [11, 14, 16, 13] * List.formPerm [19, 27]

@[expose] def u33Q1i : Equiv.Perm (Fin 28) :=
  List.formPerm [0, 11, 15, 16] * List.formPerm [1, 7, 5, 6] * List.formPerm [2, 18, 10, 26] *
    List.formPerm [4, 13, 23, 14] * List.formPerm [9, 20, 17, 12] * List.formPerm [21, 25, 22, 24]

@[expose] def u33Q1j : Equiv.Perm (Fin 28) :=
  List.formPerm [0, 14, 15, 13] * List.formPerm [1, 22, 5, 21] * List.formPerm [2, 9, 10, 17] *
    List.formPerm [4, 11, 23, 16] * List.formPerm [6, 24, 7, 25] * List.formPerm [12, 26, 20, 18]

@[expose] def u33Refs : List (List (Equiv.Perm (Fin 28))) :=
  [q8Span u33Q0i u33Q0j, q8Span u33Q1i u33Q1j]

@[expose] def u33SocCheck (_ : Unit := ()) : Bool :=
  refCheck (elemsT QSA) u33Refs && sigmaCheck sa0 u33Refs && !inQP sa0 &&
    (q8Span u33Q0i u33Q0j).all inQP && !(q8Span u33Q1i u33Q1j).all inQP

end Certificates.S7SocU33
