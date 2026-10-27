module

public import CFSG.RankThree.Co2.ClassFun
public import CFSG.RankThree.Co2.XData
public import CFSG.RankThree.Co2.ClassesCert
public meta import CFSG.RankThree.Co2.ClassFun
public meta import CFSG.RankThree.Co2.XData
public meta import CFSG.RankThree.Co2.ClassesCert
public meta import CFSG.RankThree.Co2.Rows
public meta import CFSG.Monster.B.TwoA.Co2Inv.ConjCert
public meta import CFSG.Monster.B.TwoA.Co2Inv.Data
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Monster.B.TwoA.Unitary.Semilinear
public import Certificates.Certificate8113
public import CFSG.RankThree.Co2.Classes
public meta import CFSG.RankThree.Co2.Classes
public import CFSG.RankThree.Co2.Sqrt
public meta import CFSG.RankThree.Co2.Sqrt

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster CFSG.Monster.B.Co2 CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Co2Inv

theorem sylFacts_cert : SylFacts :=
  Certificates.certificate8113

end CFSG.RankThree.Co2
