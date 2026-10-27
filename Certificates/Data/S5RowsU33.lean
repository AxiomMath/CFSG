module

public import CFSG.GH74.KGroups.U33Inputs
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks2
public import Certificates.Data.S5Rows

public section

namespace Certificates.S5RowsU33

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups Certificates.S5Rows

@[expose] def sa0 : Equiv.Perm (Fin 28) :=
  List.formPerm [1, 2] * List.formPerm [4, 11] * List.formPerm [5, 10] * List.formPerm [6, 12] *
    List.formPerm [7, 20] * List.formPerm [8, 19] * List.formPerm [9, 21] * List.formPerm [13, 14] *
    List.formPerm [16, 23] * List.formPerm [17, 22] * List.formPerm [18, 24] *
    List.formPerm [25, 26]

@[expose] def sa1 : Equiv.Perm (Fin 28) :=
  List.formPerm [1, 7] * List.formPerm [2, 9] * List.formPerm [3, 8] * List.formPerm [5, 6] *
    List.formPerm [10, 17] * List.formPerm [11, 16] * List.formPerm [12, 18] *
    List.formPerm [13, 14] * List.formPerm [19, 27] * List.formPerm [20, 26] *
    List.formPerm [21, 25] * List.formPerm [22, 24]

@[expose] def sa2 : Equiv.Perm (Fin 28) :=
  List.formPerm [1, 21] * List.formPerm [2, 20] * List.formPerm [3, 19] * List.formPerm [4, 23] *
    List.formPerm [5, 22] * List.formPerm [6, 24] * List.formPerm [7, 25] * List.formPerm [8, 27] *
    List.formPerm [9, 26] * List.formPerm [10, 12] * List.formPerm [13, 14] * List.formPerm [17, 18]

@[expose] def sa3 : Equiv.Perm (Fin 28) :=
  List.formPerm [0, 11] * List.formPerm [1, 22] * List.formPerm [3, 27] * List.formPerm [4, 14] *
    List.formPerm [5, 21] * List.formPerm [6, 24] * List.formPerm [7, 25] * List.formPerm [8, 19] *
    List.formPerm [9, 17] * List.formPerm [13, 23] * List.formPerm [15, 16] * List.formPerm [18, 26]

@[expose] def sa4 : Equiv.Perm (Fin 28) :=
  List.formPerm [0, 14, 15, 13] * List.formPerm [1, 22, 5, 21] * List.formPerm [2, 9, 10, 17] *
    List.formPerm [4, 11, 23, 16] * List.formPerm [6, 24, 7, 25] * List.formPerm [12, 26, 20, 18]

@[expose] def sa5 : Equiv.Perm (Fin 28) :=
  List.formPerm [0, 15] * List.formPerm [1, 5] * List.formPerm [2, 10] * List.formPerm [4, 23] *
    List.formPerm [6, 7] * List.formPerm [9, 17] * List.formPerm [11, 16] * List.formPerm [12, 20] *
    List.formPerm [13, 14] * List.formPerm [18, 26] * List.formPerm [21, 22] *
    List.formPerm [24, 25]

@[expose] def QSA : RawSchreierDatum 28 :=
  certificate (by decide) [sa0, sa1, sa2, sa3, sa4, sa5] [] #v[0, 1] (by decide)

@[expose] def inQP (x : Equiv.Perm (Fin 28)) : Bool :=
  U33.QP.sift x 0

@[expose] def u33RowsF1a (_ : Unit := ()) : Bool :=
  threeCycCheck (elemsT QSA) (elemsT U33.QP) inQP

@[expose] def u33RowsF1b (_ : Unit := ()) : Bool :=
  conjMulCheck (elemsT QSA) (elemsT U33.QA) inQP

@[expose] def u33RowsF1c (_ : Unit := ()) : Bool :=
  uniqueOuterCheck (elemsT QSA) inQP

end Certificates.S5RowsU33
