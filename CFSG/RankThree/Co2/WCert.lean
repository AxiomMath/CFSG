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
public import CFSG.RankThree.Co2.WCertInputs
public import CFSG.RankThree.Co2.WFacts
public import Certificates.Certificate8110

public section

namespace CFSG.RankThree.Co2

theorem wFacts_cert : WFacts :=
  Certificates.certificate8110

end CFSG.RankThree.Co2

end
