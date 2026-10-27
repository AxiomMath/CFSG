
module

public import CFSG.Monster.B.TwoA.Unitary.ActionBase
public import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Unitary.NData
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.Co2.MatrixCertBase
public import CFSG.Monster.B.Co2.MatrixIsoBase
public import CFSG.Monster.B.Co2.Order
public import CFSG.Monster.B.Co2.SimpleBase
public import CFSG.Monster.B.Short.Faithful22
public import CFSG.Monster.B.Short.ParityCentralizer
public import CFSG.Monster.B.TwoA.Base.WCls
public import CFSG.Monster.B.TwoA.Unitary.ActionInputs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.VisQuot CFSG.Monster.VisCert
  CFSG.Monster.SpinLattice CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census

@[expose] def genAct (k a : ℕ) : ℕ := Native.actD 22 n6RowArr[k]! a

@[expose] def orbitCert : NatCert := natBfs genAct 17 31 900

attribute [local instance] wLeftAction

end CFSG.Monster.B.TwoA.Unitary
