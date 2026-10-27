module

public import CFSG.RankThree.PartTwo.Census.Sporadic.Fi22W4Data
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.Fi22
public meta import CFSG.RankThree.PartTwo.Census.Sporadic.Fi22W4Data
public meta import Certificates.Data.CFSGNative.SectionRank.F3
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate8156
public import Certificates.Certificate1005
public import Certificates.Certificate9205
public meta import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem fi22W4_check : W4Data.check (ops3 77) fi22W4 = true :=
  Certificates.certificate8156

theorem four_le_localRank_three_Fi22 [Finite NativeSporadic.Fi22] :
    4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 NativeSporadic.Fi22 :=
  OpsSpec.four_le_localRank_three_of_w4Check (spec3 77) fi22W4 fi22W4_check rfl

theorem excluded433_Fi22 :
    Excluded433 (.sporadic .Fi22) :=
  excluded433_sporadic_of_four_le_localRank_three (T := NativeSporadic.Fi22)
    (fun _ => CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_Fi22)
    four_le_localRank_three_Fi22

end CFSG.RankThree.PartTwo.Census
