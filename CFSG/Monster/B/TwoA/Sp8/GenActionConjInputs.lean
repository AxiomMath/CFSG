
module

public import CFSG.Monster.B.TwoA.Sp8.GenActionDiffBase
public meta import CFSG.Monster.B.TwoA.Sp8.GenActionDiffBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371

@[expose] def genRow (k j : ℕ) : ℕ := (genRows.getD k []).getD j 0

end CFSG.Monster.B.TwoA.Sp8
