module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporGen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup

@[expose] def K315Spor : Prop :=
  ∀ s : TauCeti.SporadicName, s ∈ CFSG.RankThree.PartOne.Census3.sporadicsThm3 →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∀ Ē R : Subgroup (MulAut (TauCeti.CFSGIndex.sporadic s).Group),
        SporPlaneConf (TauCeti.CFSGIndex.sporadic s).Group p Ē R → s = .M12 ∨ s = .M22 ∨ s = .J2

end CFSG.LocalAnalysis.UniquenessCase.UCK
