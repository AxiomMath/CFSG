module

public import CFSG.GH74.KGroups.L33Inputs
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks2
public import Certificates.Data.S7SocQ8

public section

namespace Certificates.S7SocL33

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups Certificates.S5Rows
  Certificates.S7SocQ8

@[expose] def sl0 : Equiv.Perm (Fin 26) :=
  List.formPerm [1, 2] * List.formPerm [3, 5] * List.formPerm [6, 7] * List.formPerm [9, 11] *
    List.formPerm [14, 21] * List.formPerm [15, 17] * List.formPerm [18, 20] *
    List.formPerm [23, 25]

@[expose] def sl1 : Equiv.Perm (Fin 26) :=
  List.formPerm [0, 1, 8, 6] * List.formPerm [2, 11, 7, 9] * List.formPerm [3, 12] *
    List.formPerm [4, 5] * List.formPerm [13, 20] * List.formPerm [14, 17, 23, 15] *
    List.formPerm [16, 25, 22, 21] * List.formPerm [18, 24]

@[expose] def sl2 : Equiv.Perm (Fin 26) :=
  List.formPerm [0, 8] * List.formPerm [1, 6] * List.formPerm [2, 7] * List.formPerm [9, 11] *
    List.formPerm [14, 23] * List.formPerm [15, 17] * List.formPerm [16, 22] *
    List.formPerm [21, 25]

@[expose] def sl3 : Equiv.Perm (Fin 26) :=
  List.formPerm [0, 9, 8, 11] * List.formPerm [1, 7, 6, 2] * List.formPerm [3, 5] *
    List.formPerm [4, 12] * List.formPerm [13, 24] * List.formPerm [14, 21, 23, 25] *
    List.formPerm [15, 16, 17, 22] * List.formPerm [18, 20]

@[expose] def sl4 : Equiv.Perm (Fin 26) :=
  List.formPerm [0, 15, 8, 17] * List.formPerm [1, 14, 6, 23] * List.formPerm [2, 25, 7, 21] *
    List.formPerm [3, 20] * List.formPerm [4, 24] * List.formPerm [5, 18] *
    List.formPerm [9, 16, 11, 22] * List.formPerm [10, 19] * List.formPerm [12, 13]

@[expose] def l33Qi : Equiv.Perm (Fin 26) :=
  List.formPerm [0, 1, 8, 6] * List.formPerm [2, 11, 7, 9] * List.formPerm [3, 12] *
    List.formPerm [4, 5] * List.formPerm [13, 20] * List.formPerm [14, 17, 23, 15] *
    List.formPerm [16, 25, 22, 21] * List.formPerm [18, 24]

@[expose] def l33Qj : Equiv.Perm (Fin 26) :=
  List.formPerm [0, 7, 8, 2] * List.formPerm [1, 11, 6, 9] * List.formPerm [3, 4] *
    List.formPerm [5, 12] * List.formPerm [13, 18] * List.formPerm [14, 22, 23, 16] *
    List.formPerm [15, 21, 17, 25] * List.formPerm [20, 24]

@[expose] def QSL : RawSchreierDatum 26 :=
  certificate (by decide) [sl0, sl1, sl2, sl3, sl4] [] #v[0, 1] (by decide)

@[expose] def l33Refs : List (List (Equiv.Perm (Fin 26))) :=
  [q8Span l33Qi l33Qj]

@[expose] def inQP (x : Equiv.Perm (Fin 26)) : Bool :=
  L33.QP.sift x 0

@[expose] def l33SocCheck (_ : Unit := ()) : Bool :=
  refCheck (elemsT QSL) l33Refs && sigmaCheck sl4 l33Refs && !inQP sl4

end Certificates.S7SocL33
