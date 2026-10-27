
module

public import CFSG.Monster.B.TwoA.Co2Inv.CentOrderBase
public meta import CFSG.Monster.B.TwoA.Co2Inv.Data
public meta import CFSG.Monster.B.TwoA.Co2Inv.ConjCertBase
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Co2Inv.ConjCertBase
public import CFSG.Monster.B.TwoA.Co2Inv.FrameCertBase
public import CFSG.Monster.B.TwoA.Co2Inv.MrBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Co2Inv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census

@[expose] def rows6 (n : ℕ) : List ℕ := (List.range 6).map (rowOf n)

@[expose] def act6 (k n : ℕ) : ℕ :=
  encL ((List.range 6).map fun t => Native.actD 22 (cRows k) (rowOf n t))

@[expose] def valid6 (n : ℕ) : Bool := n == encL (rows6 n)

@[expose] def root6 : ℕ := encL zBasis.toList

@[expose] def sixCert : NatCert := natBfs act6 20 root6 30000

@[expose] def sixCheck : Bool :=
  natCertOK act6 20 valid6 root6 sixCert && sixCert.pts.size == 23040 &&
    (List.range 6).all fun t => rowOf root6 t == zBasis[t]!

attribute [local instance] wLeftAction

end CFSG.Monster.B.TwoA.Co2Inv
