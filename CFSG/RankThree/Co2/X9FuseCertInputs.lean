module

public import CFSG.RankThree.Co2.XSylowCert
public import CFSG.RankThree.Co2.CensusCert
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

@[expose] def inA (c : ℕ) : Bool := c == 0 || c == 2 || c == 7

@[expose] def inB (c : ℕ) : Bool := c == 1 || c == 3 || c == 5

@[expose] def inC (c : ℕ) : Bool := c == 4 || c == 6 || c == 8

end CFSG.RankThree.Co2
