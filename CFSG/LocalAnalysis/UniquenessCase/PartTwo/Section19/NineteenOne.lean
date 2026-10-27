module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Statements

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem not_concl19_8_3_of_eight_le_gamma {D : Data G} {V₀ V : Subgroup G}
    (h8 : 8 ≤ gammaN 2 D.M V) : ¬ Concl19_8_3 D V₀ V := by
  rintro ⟨hle, h6⟩
  have hcoe : ((8 : ℕ) : ℕ∞) ≤ ((2 + mSub V₀ : ℕ) : ℕ∞) := h8.trans hle
  have h8' : 8 ≤ 2 + mSub V₀ := by exact_mod_cast hcoe
  omega

theorem false_of_R19_8At_of_eight_le_gamma {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} {h : Ctx19_1 D V₀ V p L K}
    (h198 : R19_8At D V₀ V p L K h) (h8 : 8 ≤ gammaN 2 D.M V) : False :=
  not_concl19_8_3_of_eight_le_gamma h8 h198.2.2.1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
