module

public import CFSG.RankThree.PartTwo.Census.Sporadic.Co1W4Data
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import CFSG.RankThree.PartTwo.Census.Sporadic.Co1Bridge
public meta import CFSG.RankThree.PartTwo.Census.Sporadic.Co1W4Data
public meta import Certificates.Data.CFSGNative.SectionRank.F2
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate8153
public import Certificates.Certificate8154
public import Certificates.Certificate3024
public meta import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem co1W4_check : W4Data.check (ops2 24) co1W4 = true :=
  Certificates.certificate8153

theorem four_le_localRank_three_Co1 [Finite NativeSporadic.Co1] :
    4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 NativeSporadic.Co1 :=
  OpsSpec.four_le_localRank_three_of_w4Check (spec2 24) co1W4 co1W4_check rfl

theorem excluded433_Co1 :
    Excluded433 (.sporadic .Co1) :=
  @excluded433_sporadic_of_four_le_localRank_three .Co1 NativeSporadic.Co1 Units.instGroup
    (fun h => @nonempty_mulEquiv_Co1 h) four_le_localRank_three_Co1

end CFSG.RankThree.PartTwo.Census
