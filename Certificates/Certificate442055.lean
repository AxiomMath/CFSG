module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.T1Facts
import Certificates.Kernel.G2Three.Sec1T1Glue3

public section

namespace Certificates

open CFSG.OddStandard.HigherRank.G2Three.Sec1Proof CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab in
theorem certificate442055 : ∀ {G : Type} [Group G] [Finite G] (m : G23Model G), G23T1Facts m :=
  fun m => CFSG.KD.G2Three.Sec1.T1Glue.facts m

end Certificates
