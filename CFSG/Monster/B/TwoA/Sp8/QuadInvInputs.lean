
module

public import CFSG.Monster.B.TwoA.Sp8.ElemAbBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA

@[expose] def triM (j : Fin 8) : Fin 8 → ZMod 2 := bvec 8 (triRows.getD j 0)

end CFSG.Monster.B.TwoA.Sp8
