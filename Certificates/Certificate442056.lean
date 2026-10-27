module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.T5Facts
import Certificates.Kernel.G2Three.Sec1T5Glue

public section

namespace Certificates

open CFSG.OddStandard.HigherRank.G2Three.Sec1Proof CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab in
theorem certificate442056 : ∀ {G : Type} [Group G] [Finite G] (m : G23Model G), G23T5Facts m :=
  fun m => CFSG.KD.G2Three.Sec1.T5Glue.facts m

end Certificates
