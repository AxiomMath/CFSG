
module

public import CFSG.Monster.B.TwoA.Sp8.GenActionHomBase
public import CFSG.Monster.B.TwoA.Census.NatCert
public import CFSG.Monster.B.TwoA.Co2Inv.ConjCertBase
public meta import CFSG.Monster.B.TwoA.Sp8.GenActionHomBase
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Co2Inv.ConjCertBase
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.Co2
  CFSG.Monster.B.TwoA.Census

@[expose] def vecAct (k x : ℕ) : ℕ := Native.actD 8 (genArr k) x

@[expose] def vecValid (x : ℕ) : Bool := decide (x < 256)

@[expose] def vecCert : NatCert := natBfs vecAct 45 1 300

@[expose] def tupAct (k n : ℕ) : ℕ :=
  Co2Inv.encL ((List.range 8).map fun t => Native.actD 8 (genArr k) (Co2Inv.rowOf n t))

@[expose] def tupValid (n : ℕ) : Bool :=
  n == Co2Inv.encL ((List.range 8).map (Co2Inv.rowOf n)) &&
    (List.range 8).all fun t => decide (Co2Inv.rowOf n t < 256)

@[expose] def tupRoot : ℕ := Co2Inv.encL ((List.range 8).map (2 ^ ·))

@[expose] def tupCert : NatCert := natBfs tupAct 23 tupRoot 200

end CFSG.Monster.B.TwoA.Sp8
