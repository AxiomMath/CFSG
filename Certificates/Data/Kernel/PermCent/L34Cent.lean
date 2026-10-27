module

public import CFSG.GH74.KGroups.L34Inputs

public section

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5124

open CFSG.Sporadic.Schreier CFSG.Certificates

@[expose] def hc1 : Equiv.Perm (Fin 42) :=
  List.formPerm [1, 13, 17, 5] * List.formPerm [2, 15, 19, 8] * List.formPerm [3, 14, 20, 7] * List.formPerm [4, 16, 18, 6] * List.formPerm [10, 11] * List.formPerm [22, 26, 38, 34] * List.formPerm [23, 29, 40, 36] * List.formPerm [24, 28, 41, 35] * List.formPerm [25, 27, 39, 37] * List.formPerm [31, 32]

@[expose] def hc2 : Equiv.Perm (Fin 42) :=
  List.formPerm [0, 24, 10, 41, 9, 28] * List.formPerm [1, 26, 4, 37, 7, 33, 20, 34, 19, 40, 13, 21] * List.formPerm [2, 32, 16, 22, 14, 23, 18, 31, 8, 38, 5, 27] * List.formPerm [3, 39, 17, 29] * List.formPerm [6, 36, 15, 25] * List.formPerm [11, 35] * List.formPerm [12, 30]

@[expose] def hGens : List (Equiv.Perm (Fin 42)) := [hc1, hc2]

@[expose] def QH : RawSchreierDatum 42 :=
  certificate (by decide) hGens [[-1, -2, -2], [-2, -2, 1, -2, 1, -2, 1], [1, 1, 2, -1, 2, 2, 2]]
    #v[1, 2, 3] (by decide)

@[expose] def kc1 : Equiv.Perm (Fin 42) :=
  List.formPerm [0, 10] * List.formPerm [1, 3, 8, 6] * List.formPerm [2, 19, 7, 14] * List.formPerm [4, 13, 5, 18] * List.formPerm [9, 11] * List.formPerm [15, 20, 17, 16] * List.formPerm [21, 25, 32, 39] * List.formPerm [22, 27, 26, 40] * List.formPerm [23, 34, 37, 38] * List.formPerm [24, 41] * List.formPerm [28, 35] * List.formPerm [29, 33, 36, 31]

@[expose] def kc2 : Equiv.Perm (Fin 42) :=
  List.formPerm [0, 11] * List.formPerm [1, 3, 16, 15] * List.formPerm [2, 5, 13, 19] * List.formPerm [4, 18, 14, 7] * List.formPerm [6, 20, 17, 8] * List.formPerm [9, 10] * List.formPerm [21, 40, 31, 23] * List.formPerm [22, 39, 34, 36] * List.formPerm [24, 41] * List.formPerm [25, 38, 29, 26] * List.formPerm [27, 33, 37, 32] * List.formPerm [28, 35]

@[expose] def kGens : List (Equiv.Perm (Fin 42)) := [kc1, kc2]

end CFSG.Certificates.Kernel.PkCV.KGrp.K5124
