module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3NoPairR
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2122NPSp4Case
import CFSG.LocalAnalysis.UniquenessCase.UC22S2122NPJ4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedThree)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s21_22R3NoPairR_of_inputs {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (hK3 : StronglyEmbeddedThree)
    (h211 : S21_1 D Ch) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n)
    (h218 : S21_8N D Ch) (h218UR : S21_8UR D Ch)
    (hσ : ∀ r : ℕ, r.Prime → 7 ≤ r → 3 ≤ CFSG.Open.pRank r D.M → r ∈ D.sig) :
    S21_22R3NoPairR D Ch := by
  intro h1930 c H₁ hH₁ H₂ hH₂ hL0 hfX _ _ _ _ _ hlast
  rcases hlast with ⟨L, hL, hSp | hJ⟩
  · obtain ⟨hLN, a, ha, hX⟩ := hSp
    exact uc22s2122np_false_of_sp4 hSg hK3 h211 hn3 h218 h218UR hσ h1930 c hH₁ hH₂
      hL0 hfX hL hLN ha hX
  · obtain ⟨h2, hJ1, hn, hOpp, hU⟩ := hJ
    exact uc22s2122np_false_of_J1 h211 h1930 c hH₁ hH₂ hL0 hfX hL h2 hJ1 hn hOpp hU

end CFSG.LocalAnalysis.UniquenessCase.UC22
