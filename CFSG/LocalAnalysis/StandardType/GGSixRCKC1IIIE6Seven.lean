module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIFive
import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthKSLOrder
import Mathlib.Tactic.NormNum

public section

namespace CFSG.StandardType.RCKC1

open CFSG CFSG.Assembly CFSG.StandardType





theorem not_e6_seven_label_of_row_III_le
    {X : Type} [Group X] [Finite X] {J K : Subgroup X}
    (hrow : GGSixRCKJRow .III J) (hJK : J ≤ K) :
    ¬ ∃ lab : LargeEvenLabel,
      lab ∈ [⟨.A, 2, 1⟩, ⟨.triD4, 0, 1⟩] ∧
      GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) := by
  rintro ⟨lab, hmem, hlabel⟩
  have h5 := five_dvd_card_centerQuot_of_row_III_le hrow hJK
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · rw [← ggKSL_labOrd_eq (by simp [LargeEvenInLambda2]) hlabel] at h5
    exact (by decide +kernel : ¬ 5 ∣ SporadicShape.labOrd ⟨.A, 2, 1⟩) h5
  · rw [← ggKSL_labOrd_eq (by simp [LargeEvenInLambda2]) hlabel] at h5
    exact (by decide +kernel : ¬ 5 ∣ SporadicShape.labOrd ⟨.triD4, 0, 1⟩) h5

end CFSG.StandardType.RCKC1
