
module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.B.Rep4371.Bits
public import CFSG.Monster.B.Short.Rootless
public import CFSG.Monster.Generated.Data
public import CFSG.Monster.VisQuot.Monomial
public import Certificates.Data.CFSGNative.MonsterB.DyadicElim

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.VisQuot CFSG.Monster.B.Rep4371
open scoped Matrix

@[expose] def gramPauli : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  Matrix.of fun k l => if (k : ℕ) + 11 = l ∨ (l : ℕ) + 11 = k then 1 else 0

end CFSG.Monster.B
