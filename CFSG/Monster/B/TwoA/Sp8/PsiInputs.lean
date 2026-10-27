
module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.B.Rep4371.Bits
public import CFSG.Monster.B.Short.Rootless
public import CFSG.Monster.B.TwoA.Base.CodeCheck
public import CFSG.Monster.B.TwoA.Census.SymTrace
public import CFSG.Monster.B.TwoA.Co2Inv.Data
public import CFSG.Monster.Generated.Data
public import CFSG.Monster.VisCert.Basis

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371
  CFSG.Monster.B.TwoA.Census CFSG.Monster.VisCert CFSG.Monster.B.Co2

@[expose] def twoD (i : ℕ) : ℤ := if i < 8 then 2 else 0

end CFSG.Monster.B.TwoA.Sp8
