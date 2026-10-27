module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XInnerSpec
import Certificates.Kernel.HN1408.XInnerGlue

public section

namespace Certificates

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section4 in
theorem certificate441899 : Nat.card ↥P1408 = 177408000 → XModel.XNFacts :=
  CFSG.KD.HN1408.XInner.xInnerK

end Certificates

end
