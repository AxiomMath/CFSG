module

public import CFSG.RankThree.PartTwo.Sec21.FF84Defs
public import CFSG.RankThree.PartTwo.Sec21.FF84S3Model

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8 A8s)

@[expose] def cc : P8 := Equiv.swap 0 1 * Equiv.swap 1 2
@[expose] def dd : P8 := Equiv.swap 3 4 * Equiv.swap 4 5
@[expose] def Pm : Subgroup P8 := Subgroup.closure {cc, dd}
@[expose] def v4 (a b c d : Fin 8) : Subgroup P8 :=
  Subgroup.closure {Equiv.swap a b * Equiv.swap c d, Equiv.swap a c * Equiv.swap b d}
@[expose] def Ua : Subgroup P8 := v4 3 4 5 6 ⊔ v4 0 1 2 7
@[expose] def Ub : Subgroup P8 := v4 3 4 5 7 ⊔ v4 0 1 2 6

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
