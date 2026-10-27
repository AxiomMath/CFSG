module

public import CFSG.RankThree.PartTwo.Sec4.Census.Open46
import CFSG.RankThree.PartTwo.Sec4.Census.Simple46
import CFSG.RankThree.PartTwo.Sec4.Census.Cover46
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

theorem rank3II_4_6_of (h41 : Item4_1) (h42 : Item4_2) (h43 : Item4_3) (hin : Inputs46) :
    Item4_6 := by
  intro G _ _ hG h3 L hL
  have hq : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L) := hL.2.2
  have hS := sectionFourHyp_thetaQuotient h41 hG hL
  have hZ3 := isPGroup_center_thetaQuotient L
  by_cases hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥
  · have : IsSimpleGroup (L ⧸ aschbacherSolvableCore 3 L) := isSimpleGroup_of_center_eq_bot hq hZ
    obtain ⟨z, hz, hz3⟩ := exists_orderOf_eq_three_of_dvd h3
    exact isList46_of_list42 hZ
      (localRank_thetaQuotient_le_two hG hz hz3 (not_mem_of_center_eq_bot hz hz3 hZ)) hin.rank
      hin.bridge (h42 _ hS inferInstance (exists_ne_of_isQuasisimple hq))
  · have h3Z : 3 ∣ Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ3
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hZ (Subgroup.card_eq_one.mp (by rw [hk, pow_zero]))
      rw [hk]
      exact dvd_pow_self 3 hk0
    exact isList46_of_cover hS (sectionFourHyp_quotient_center h41 hS hq) hq hZ3 hZ hin.cover
      (h43 _ hS hq h3Z)

end CFSG.RankThree.PartTwo.Sec4.Census
