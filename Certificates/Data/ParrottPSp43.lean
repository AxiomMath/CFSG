module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelData
public import CFSG.GH74.KGroups.PermCheck
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelData

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GH74.KGroups

local notation "P45" => Equiv.Perm (Fin 45)

abbrev t : P45 := x45

@[expose] def u : P45 :=
  List.formPerm [3, 9] * List.formPerm [4, 10] * List.formPerm [5, 11] * List.formPerm [6, 12] *
  List.formPerm [7, 13] * List.formPerm [8, 14] * List.formPerm [25, 35] * List.formPerm [26, 44] *
  List.formPerm [27, 42] * List.formPerm [28, 43] * List.formPerm [29, 38] *
  List.formPerm [30, 36] * List.formPerm [31, 37] * List.formPerm [32, 41] *
  List.formPerm [33, 39] * List.formPerm [34, 40]

@[expose] def v : P45 :=
  List.formPerm [3, 6] * List.formPerm [4, 8] * List.formPerm [5, 7] * List.formPerm [9, 12] *
  List.formPerm [10, 14] * List.formPerm [11, 13] * List.formPerm [17, 22] *
  List.formPerm [18, 19] * List.formPerm [20, 24] * List.formPerm [25, 35] *
  List.formPerm [26, 36] * List.formPerm [27, 42] * List.formPerm [28, 39] *
  List.formPerm [29, 38] * List.formPerm [30, 44] * List.formPerm [31, 41] *
  List.formPerm [32, 37] * List.formPerm [33, 43] * List.formPerm [34, 40]

@[expose] def sigma1 : P45 :=
  List.formPerm [9, 11, 10] * List.formPerm [12, 14, 13] * List.formPerm [15, 35, 25] *
  List.formPerm [16, 44, 30] * List.formPerm [17, 42, 31] * List.formPerm [18, 43, 29] *
  List.formPerm [19, 38, 33] * List.formPerm [20, 36, 34] * List.formPerm [21, 37, 32] *
  List.formPerm [22, 41, 27] * List.formPerm [23, 39, 28] * List.formPerm [24, 40, 26]

@[expose] def sigma2 : P45 :=
  List.formPerm [3, 5, 4] * List.formPerm [6, 8, 7] * List.formPerm [15, 25, 35] *
  List.formPerm [16, 26, 36] * List.formPerm [17, 27, 37] * List.formPerm [18, 28, 38] *
  List.formPerm [19, 29, 39] * List.formPerm [20, 30, 40] * List.formPerm [21, 31, 41] *
  List.formPerm [22, 32, 42] * List.formPerm [23, 33, 43] * List.formPerm [24, 34, 44]

@[expose] def alpha1 : P45 :=
  List.formPerm [1, 12, 2, 9] * List.formPerm [3, 23, 6, 21] * List.formPerm [4, 43, 7, 41] *
  List.formPerm [5, 33, 8, 31] * List.formPerm [10, 11, 13, 14] * List.formPerm [15, 16] *
  List.formPerm [17, 38, 19, 42] * List.formPerm [18, 29, 22, 27] * List.formPerm [20, 24] *
  List.formPerm [25, 26] * List.formPerm [28, 39, 32, 37] * List.formPerm [30, 34] *
  List.formPerm [35, 36] * List.formPerm [40, 44]

@[expose] def beta1 : P45 :=
  List.formPerm [1, 14, 2, 11] * List.formPerm [3, 39, 6, 37] * List.formPerm [4, 29, 7, 27] *
  List.formPerm [5, 19, 8, 17] * List.formPerm [9, 10, 12, 13] * List.formPerm [15, 24] *
  List.formPerm [16, 20] * List.formPerm [18, 41, 22, 43] * List.formPerm [21, 32, 23, 28] *
  List.formPerm [25, 34] * List.formPerm [26, 30] * List.formPerm [31, 42, 33, 38] *
  List.formPerm [35, 44] * List.formPerm [36, 40]

@[expose] def alpha2 : P45 :=
  List.formPerm [1, 6, 2, 3] * List.formPerm [4, 5, 7, 8] * List.formPerm [9, 23, 12, 21] *
  List.formPerm [10, 28, 13, 32] * List.formPerm [11, 39, 14, 37] * List.formPerm [15, 16] *
  List.formPerm [17, 29, 19, 27] * List.formPerm [18, 38, 22, 42] * List.formPerm [20, 24] *
  List.formPerm [25, 30] * List.formPerm [26, 34] * List.formPerm [31, 43, 33, 41] *
  List.formPerm [35, 44] * List.formPerm [36, 40]

@[expose] def beta2 : P45 :=
  List.formPerm [1, 8, 2, 5] * List.formPerm [3, 4, 6, 7] * List.formPerm [9, 33, 12, 31] *
  List.formPerm [10, 38, 13, 42] * List.formPerm [11, 19, 14, 17] * List.formPerm [15, 24] *
  List.formPerm [16, 20] * List.formPerm [18, 32, 22, 28] * List.formPerm [21, 41, 23, 43] *
  List.formPerm [25, 26] * List.formPerm [27, 39, 29, 37] * List.formPerm [30, 34] *
  List.formPerm [35, 40] * List.formPerm [36, 44]

@[expose] def beta : P45 :=
  List.formPerm [0, 15] * List.formPerm [1, 35, 2, 25] * List.formPerm [3, 9, 12, 6] *
  List.formPerm [4, 11, 13, 8] * List.formPerm [5, 10, 14, 7] * List.formPerm [17, 44, 19, 26] *
  List.formPerm [18, 30, 22, 36] * List.formPerm [20, 24] * List.formPerm [21, 40, 23, 34] *
  List.formPerm [27, 42, 38, 29] * List.formPerm [28, 31, 41, 39] * List.formPerm [32, 37, 43, 33]

end CFSG.RankThree.GF2n.Parrott
