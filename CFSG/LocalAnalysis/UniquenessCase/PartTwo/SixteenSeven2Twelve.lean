module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2V1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem sixteen_seven2_twelve (D : Data G) (h10 : R16_10_1 D) (h11 : R16_11 D) : R16_12 D := by
  intro V₀ V L hV hC
  have h125 : Hyp125 D V₀ V := hC.setting.hyp16.hyp125
  have ha : ¬ centralizer (E3.cClos V D.k D.T : Set G) ≤ D.M := by
    intro hcM
    obtain ⟨H₀, hH₀⟩ := h125.exists_hyp124Min
    have h1 := h10 V₀ V L hV hC H₀ hH₀
    have h2 : H₀ ≤ D.M := by
      rw [← h1]
      exact sup_le (inf_le_right.trans hcM) (inf_le_right.trans (h11 V₀ V L hV hC))
    exact hH₀.1.2.1 h2
  have hb : V₀ = ⊥ := by
    by_contra hne
    exact ha (TwelveTwentyTwo.centralizer_cClos_le h125 hne D.k)
  exact ⟨ha, hb, fun h => s16c167_v1Sub_eq_bot_of_case9 D hV hb h⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
