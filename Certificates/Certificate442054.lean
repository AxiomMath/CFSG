module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.ModelDef
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FactsS
import Certificates.Kernel.G2Three.Sec1T3Glue2

public section

namespace Certificates

open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.OddStandard.HigherRank.G2Three.Sec1Proof in
theorem certificate442054 : ∀ {G : Type} [Group G] [Finite G] (m : G23Model G),
    (frameOf m).Fact11 m.L ∧ (frameOf m).Fact12 ∧ (frameOf m).Fact13 ∧ (frameOf m).Fact14 ∧
      (frameOf m).Fact15 :=
  fun m => CFSG.KD.G2Three.Sec1T3.Glue.s3_facts m

end Certificates
