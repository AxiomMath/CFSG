module

public import CFSG.RankThree.Co2.X9FuseCert
public import CFSG.RankThree.Co2.JUniqueCert
public import CFSG.RankThree.Co2.XSylowCert
public import CFSG.RankThree.Co2.CensusCert
public meta import CFSG.RankThree.Co2.X9FuseCert
public meta import CFSG.RankThree.Co2.JUniqueCert
public meta import CFSG.RankThree.Co2.XSylowCert
public meta import CFSG.RankThree.Co2.CensusCert
public meta import CFSG.RankThree.Co2.Rows
public meta import CFSG.Monster.B.TwoA.Co2Inv.ConjCert
public meta import CFSG.Monster.B.TwoA.Co2Inv.Data
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix

public noncomputable section

namespace CFSG.RankThree.Co2

open CFSG.Monster CFSG.Monster.B.Co2 CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Co2Inv

@[expose] def gLab (c : ℕ) : ℕ :=
  if inA c then 1 else if inB c then 2 else if inC c || c == 9 then 3 else 0

@[expose] def sigma (t₂ t₃ m : ℕ) : ℕ :=
  (if m.testBit 0 then 2 else 0) ^^^ (if m.testBit 1 then 1 else 0) ^^^
    (if m.testBit 2 then t₂ else 0) ^^^ (if m.testBit 3 then t₃ else 0)

end CFSG.RankThree.Co2
