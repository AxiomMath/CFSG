module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.SqFacts
import Certificates.Kernel.HN1408.SqZFacts

public section

namespace Certificates

open CFSG.EvenSporadicStandard.HNRecog in
theorem certificate26774 : Nat.card ↥P1408 = 177408000 → SqFacts :=
  CFSG.KD.HN1408.SqZ.sq_facts

end Certificates

end
