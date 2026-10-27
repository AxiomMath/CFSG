module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3ThirteenOneA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3ThirteenOneB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3ThirteenOneC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r16_13_1_holds (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h111 : W3Thm111 G)
    (h12 : R16_12 D) (h13b : R16_13_2 D) (hM : S16GapMGtOne D) (hBC : S16GapInspBC D)
    (hAE : S16GapAEmpty D) : R16_13_1 D := by
  intro V₀ V L hV hc
  obtain ⟨h12a, h12b, h12c⟩ := h12 V₀ V L hV hc
  subst h12b
  have hm : 1 < mBar D.M ⊥ V hV := hM V L hV hc
  refine ⟨s16c167_exists_choice1613 D h61 hBC hV hc h12a, fun A hA g hAg => ?_⟩
  have hnle : ¬ conjSubgroup V g ≤ D.M :=
    s16c167_not_le_M_of_choice D hx h61 hV hc hm rfl h12c hA hAg
  exact ⟨hnle, fun hVM =>
    s16c167_case168_2_of_le_conj D hx h61 h111 hAE hM hV hc (h13b ⊥ V L hV hc) hVM hnle⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
