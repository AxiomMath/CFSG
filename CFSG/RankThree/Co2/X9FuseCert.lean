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
public import CFSG.RankThree.Co2.X9FuseCertInputs
public import Certificates.Certificate8112

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster CFSG.Monster.B.Co2 CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Co2Inv

theorem fuseCounts_cert :
    fuseN {0, 2, 7} {4, 6, 8} {9} = 32 ∧ fuseN {0, 2, 7} {9} {4, 6, 8} = 0 ∧
      fuseN {0, 2, 7} {4, 6, 8} {1, 3, 5, 9} = 68 ∧ fuseN {0, 2, 7} {1, 3, 5, 9} {4, 6, 8} = 36 :=
  Certificates.certificate8112

end CFSG.RankThree.Co2
