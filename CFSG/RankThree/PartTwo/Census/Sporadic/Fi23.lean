module

public import CFSG.RankThree.PartTwo.Census.Sporadic.Fi23W4Data
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.Sporadic.Bridge.Fi23Surj
public meta import CFSG.RankThree.PartTwo.Census.Sporadic.Fi23W4Data
public meta import Certificates.Data.CFSGNative.SectionRank.F3
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate8157
public import Certificates.Certificate1012
public import Certificates.Certificate9111
public import Certificates.Certificate9206
public meta import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem fi23W4_check : W4Data.check (ops3 253) fi23W4 = true :=
  Certificates.certificate8157

theorem four_le_localRank_three_Fi23 [Finite NativeSporadic.Fi23] :
    4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 NativeSporadic.Fi23 :=
  OpsSpec.four_le_localRank_three_of_w4Check (spec3 253) fi23W4 fi23W4_check rfl

theorem excluded433_Fi23 :
    Excluded433 (.sporadic .Fi23) :=
  @excluded433_sporadic_of_four_le_localRank_three .Fi23 NativeSporadic.Fi23 Units.instGroup
    (fun _ => CFSG.Sporadic.Bridge.Fi23.nonempty_mulEquiv.map MulEquiv.symm)
    four_le_localRank_three_Fi23

end CFSG.RankThree.PartTwo.Census
