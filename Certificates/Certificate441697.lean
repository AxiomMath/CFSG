module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TabXFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.WordSub
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableIData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Elems
import Certificates.Kernel.HN1408.TabXGlue
public import CFSG.Certificates.CosetTableShort
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.Enum
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCongrK
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Iso
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace Certificates

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3Model in
theorem certificate441697 : Nat.card ↥P1408 = 177408000 →
    TabXFacts pA CFSG.EvenSporadicStandard.HNRecog.pZ pB pZ₁ (HaradaModel.wordSubgroupP nWords1) :=
  CFSG.KD.HN1408.TabX.tabXFacts_K

end Certificates

end
