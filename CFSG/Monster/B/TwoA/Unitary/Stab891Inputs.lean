
module

public import CFSG.Monster.B.TwoA.Unitary.WStabBase
public meta import CFSG.Monster.B.TwoA.Unitary.NData
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.VisQuot CFSG.Monster.VisCert CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census

attribute [local instance] wLeftAction

@[expose] def spanIdxN : List ℕ :=
  (List.range 21).map fun i => (List.range 891).findIdx fun j => n6VecArr[j]! == n6SpanArr[i]!

end CFSG.Monster.B.TwoA.Unitary
