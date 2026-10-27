module

public import Certificates.Data.ParrottPSp43

public section

namespace CFSG.RankThree.GF2n.Parrott

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def b5 : P45 :=
  List.formPerm [0, 23, 16, 40, 42] * List.formPerm [1, 25, 2, 38, 21] *
  List.formPerm [3, 13, 41, 30, 19] * List.formPerm [4, 24, 10, 9, 44] *
  List.formPerm [5, 37, 26, 18, 12] * List.formPerm [6, 36, 14, 20, 8] *
  List.formPerm [7, 22, 31, 28, 43] * List.formPerm [11, 17, 32, 33, 39] *
  List.formPerm [15, 27, 29, 35, 34]

end CFSG.RankThree.GF2n.Parrott
