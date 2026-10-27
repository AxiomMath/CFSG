module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM12ModelData
public import CFSG.GH74.KGroups.PermCheck
public import Certificates.Data.S7SocQ8
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreOuter

public section

namespace Certificates.S7SocM12

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups Certificates.S5Rows
  Certificates.S7SocQ8

@[expose] def sm0 : Equiv.Perm (Fin 24) :=
  List.formPerm [2, 10] * List.formPerm [4, 6] * List.formPerm [7, 9] * List.formPerm [8, 11] *
    List.formPerm [15, 17] * List.formPerm [16, 23] * List.formPerm [18, 20] *
    List.formPerm [19, 21]

@[expose] def sm1 : Equiv.Perm (Fin 24) :=
  List.formPerm [1, 2] * List.formPerm [3, 10] * List.formPerm [4, 6] * List.formPerm [9, 11] *
    List.formPerm [12, 14] * List.formPerm [13, 16] * List.formPerm [15, 20] *
    List.formPerm [22, 23]

@[expose] def sm2 : Equiv.Perm (Fin 24) :=
  List.formPerm [1, 3] * List.formPerm [2, 10] * List.formPerm [7, 8] * List.formPerm [9, 11] *
    List.formPerm [13, 22] * List.formPerm [15, 20] * List.formPerm [16, 23] *
    List.formPerm [17, 18]

@[expose] def sm3 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 1, 5, 3] * List.formPerm [2, 4, 10, 6] * List.formPerm [12, 22, 14, 13] *
    List.formPerm [15, 17] * List.formPerm [16, 19, 23, 21] * List.formPerm [18, 20]

@[expose] def sm4 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 5] * List.formPerm [1, 3] * List.formPerm [2, 10] * List.formPerm [4, 6] *
    List.formPerm [12, 14] * List.formPerm [13, 22] * List.formPerm [16, 23] *
    List.formPerm [19, 21]

@[expose] def sm5 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 6, 5, 4] * List.formPerm [1, 10, 3, 2] * List.formPerm [12, 21, 14, 19] *
    List.formPerm [13, 16, 22, 23] * List.formPerm [15, 20] * List.formPerm [17, 18]

@[expose] def sm6 : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 13] * List.formPerm [1, 12] * List.formPerm [2, 21, 10, 19] *
    List.formPerm [3, 14] * List.formPerm [4, 23, 6, 16] * List.formPerm [5, 22] *
    List.formPerm [7, 15, 9, 17] * List.formPerm [8, 20, 11, 18]

@[expose] def m12Q0i : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 3, 5, 1] * List.formPerm [2, 6, 10, 4] * List.formPerm [12, 13, 14, 22] *
    List.formPerm [15, 17] * List.formPerm [16, 21, 23, 19] * List.formPerm [18, 20]

@[expose] def m12Q0j : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 6, 5, 4] * List.formPerm [1, 10, 3, 2] * List.formPerm [12, 21, 14, 19] *
    List.formPerm [13, 16, 22, 23] * List.formPerm [15, 20] * List.formPerm [17, 18]

@[expose] def m12Q1i : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 4, 5, 6] * List.formPerm [1, 10, 3, 2] * List.formPerm [7, 8] *
    List.formPerm [9, 11] * List.formPerm [12, 19, 14, 21] * List.formPerm [13, 16, 22, 23]

@[expose] def m12Q1j : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 10, 5, 2] * List.formPerm [1, 6, 3, 4] * List.formPerm [7, 11] *
    List.formPerm [8, 9] * List.formPerm [12, 23, 14, 16] * List.formPerm [13, 19, 22, 21]

@[expose] def QSM : RawSchreierDatum 24 :=
  certificate (by decide) [sm0, sm1, sm2, sm3, sm4, sm5, sm6] [] #v[0, 1, 2] (by decide)

@[expose] def inD (x : Equiv.Perm (Fin 24)) : Bool :=
  m12D.sift x 0

@[expose] def m12SocGens (_ : Unit := ()) : Bool :=
  [sm0, sm1, sm2, sm3, sm4, sm5, sm6].all fun g => inD g || inD (m12Sigma * g)

@[expose] def m12Refs : List (List (Equiv.Perm (Fin 24))) :=
  [q8Span m12Q0i m12Q0j, q8Span m12Q1i m12Q1j]

@[expose] def m12SocCheck (_ : Unit := ()) : Bool :=
  refCheck (elemsT QSM) m12Refs && sigmaCheck sm6 m12Refs && !inD sm6 &&
    m12Refs.all fun R => R.all inD

end Certificates.S7SocM12
