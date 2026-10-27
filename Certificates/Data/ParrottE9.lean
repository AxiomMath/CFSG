module

public import Certificates.Data.ParrottPSp43

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GH74.KGroups

@[expose] def e9 : Equiv.Perm (Fin 45) :=
  List.formPerm [0, 6, 1] * List.formPerm [2, 3, 4] * List.formPerm [5, 8, 7] *
  List.formPerm [9, 37, 40, 11, 32, 26, 10, 21, 24] *
  List.formPerm [12, 23, 38, 14, 39, 33, 13, 28, 19] *
  List.formPerm [15, 16, 42, 35, 44, 31, 25, 30, 17] *
  List.formPerm [18, 27, 34, 43, 22, 20, 29, 41, 36]

end CFSG.RankThree.GF2n.Parrott
