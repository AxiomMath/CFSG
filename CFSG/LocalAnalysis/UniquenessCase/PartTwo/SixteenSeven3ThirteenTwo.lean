module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3ThirteenOneA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3ThirteenTwoEnd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3GapInspA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem r16_13_2_holds (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h111 : W3Thm111 G)
    (hSg : UC6S846.SigmaStd D) (h12 : R16_12 D) (hM : S16GapMGtOne D) (hBC : S16GapInspBC D)
    (hA : S16GapInspA D) (hAE : S16GapAEmpty D) (hβ : S16GapBetaBound D) : R16_13_2 D := by
  intro V₀ V L hV hc
  obtain ⟨h12a, h12b, h12c⟩ := h12 V₀ V L hV hc
  subst h12b
  by_contra hn
  by_cases hcomm : ⁅oddBar D.M ⊥ V hV, barSub ⊥ V hV (E3.wClos V D.k D.T)⁆ = ⊥
  · obtain ⟨A, hAch⟩ := s16c167_exists_choice1613 D h61 hBC hV hc h12a
    obtain ⟨hAΓ, hdisj⟩ := hAch
    rcases hdisj with hne | ⟨h9, -⟩
    · exact hne (le_bot_iff.1
        ((Subgroup.commutator_mono le_rfl (barSub_mono ⊥ V hV (E3.le_wClos hAΓ))).trans hcomm.le))
    · exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h9)))))
  · by_cases hr : ∃ r : ℕ, 3 < r ∧ Case168_4With D ⊥ V hV L r
    · exact s16c167_false_of_case4_gt3 D hx h61 h111 hM hAE hβ hV hc h12c hr hcomm
    · exact s16c167_false_of_insp1613U D h61 (B2F.isPGroup_of_isElemAbelian hV)
        (s15_13A_le_T hc.setting.hyp16.hyp125) h12a (hA hSg V L hV hc hn hcomm hr)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
