module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5DDefs
import Certificates.Kernel.HN1408.D442204Glue

public section

namespace Certificates

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Simple2S5 in
theorem certificate442204 : Nat.card ↥P1408 = 177408000 → DFacts :=
  CFSG.KD.HN1408.D442204.dFactsK

end Certificates

end
