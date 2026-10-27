module

public import CFSG.RankThree.PartTwo.Sec21.FF84S23Main
public import CFSG.RankThree.PartTwo.Sec21.FF84S23Reduce

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open CFSG

theorem ff84_2_3_reduced_of (hKF1 : FF84KF1) (hKS : FF84KSOut) : FF84_2_3_Reduced := by
  intro H _ _ hK hO P P₁ P₂ hsyl hP hc1 hc2 hsup hinf hsc1 hsc2
  have h : Red3 P P₁ P₂ := ⟨hsyl, hP, hc1, hc2, hsup, hinf, hsc1, hsc2⟩
  by_cases hex : ∃ C : Subgroup H, IsComponent C
  · obtain ⟨C, hC⟩ := hex
    rcases h.comp_card hO hC with h3 | h9
    · exact h.comp_card_three hKS hK hO hC h3
    · exact (h.comp_card_nine_false hKF1 hK hO hC h9).elim
  · have hno : ∀ C : Subgroup H, ¬ IsComponent C := fun C hC => hex ⟨C, hC⟩
    exact h.no_comp_case hO hno

theorem ff84_2_3_of (hKF1 : FF84KF1) (hKS : FF84KSOut) : FF84_2_3 :=
  ff84_2_3_of_reduced (ff84_2_3_reduced_of hKF1 hKS)

end CFSG.RankThree.PartTwo.Sec21.FF84
