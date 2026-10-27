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

@[expose] def wWords : Array (List ℕ) := #[[2], [9], [12, 7, 6, 20, 6, 12, 27, 41, 27, 28, 33],
  [17, 7, 14, 6, 20, 6, 12, 27, 41, 27, 35, 28, 38],
  [17, 20, 17, 6, 20, 6, 12, 27, 41, 27, 38, 41, 38]]

end CFSG.RankThree.Co2
