module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.B.Rep4371.Model
public import CFSG.Monster.B.Short.AxisOrbit
public import CFSG.Monster.B.TwoA.Census.SymTrace
public import CFSG.Monster.Visible.PermBeta
public import Certificates.Data.CFSGNative.MonsterB.CosetEnum

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.TwoA.Census
  CFSG.Monster.B.Rep4371 CFSG.Monster.B.Short
open scoped IsMulCommutative

@[expose] def octFixTest (tA tB : Array Model.Pauli) (n : ℕ) : Bool :=
  let p := Native.Pauli.mul tA[n % 2 ^ 12]! tB[n / 2 ^ 12 % 2 ^ 12]!
  !((p.2.1 % 2 ^ 12 == n % 2 ^ 12) && (p.2.2 % 2 ^ 12 == n / 2 ^ 12 % 2 ^ 12)) || !p.1

@[expose] def octFixCount (tA tB : Array Model.Pauli) : ℕ :=
  Native.CosetEnum.countBelow (octFixTest tA tB) (2 ^ 24) 0

end CFSG.Monster.B.CTIB
