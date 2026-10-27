module

public import CFSG.RankThree.PartTwo.Sec6.Item65UsedStatement
public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.RankThree.PartTwo.KFacts.KS6OuterIndex
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Sec6.Item66
import CFSG.RankThree.PartTwo.Sec6.Item65Used
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec6.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

theorem rank3II_6_6Used (h65 : Item6_5Used) : Item6_6 := by
  intro G _ _ hG A hA L hL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := A ⊓ thetaQuotCentralizer L with hD
  have hAab := hA.1.1
  have hDab : CFSG.Assembly.IsElemAbelian 3 D := Sec5.isElemAbelian_of_le hAab inf_le_left
  have hD3 : IsPGroup 3 D := Sec5.isPGroup_of_isElemAbelian hDab
  obtain ⟨k, hk⟩ := hD3.exists_card_eq
  by_contra hnc
  have hk2 : 2 ≤ k := by
    by_contra hk2
    apply hnc
    interval_cases k
    · have : Subsingleton D := Finite.card_le_one_iff_subsingleton.mp (by rw [hk]; norm_num)
      exact isCyclic_of_subsingleton
    · exact isCyclic_of_prime_card (p := 3) (by rw [hk, pow_one])
  obtain ⟨B', hB'⟩ := Sylow.exists_subgroup_card_pow_prime (G := D) 3 (n := 2)
    (by rw [hk]; exact pow_dvd_pow 3 hk2)
  set B := B'.map D.subtype with hBdef
  have hBD : B ≤ D := Subgroup.map_subtype_le _
  have hB9 : Nat.card B = 9 := by
    rw [hBdef, Subgroup.card_map_of_injective D.subtype_injective, hB']
    norm_num
  have hBab : CFSG.Assembly.IsElemAbelian 3 B := Sec5.isElemAbelian_of_le hDab hBD
  have hLA := lStar_subset A hL
  obtain ⟨b, hbB, hb1, K, hK, hYK⟩ : ∃ b ∈ B, b ≠ 1 ∧ ∃ K ∈ thetaComponentsAt 3 b,
      inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {b}) ⊔
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {b})) < K := by
    have h65' := h65 G hG A hA L hLA B hBab hB9 hBD
    by_cases hEx : ∃ E ∈ collectionIn (partTwoE G) (A ⊔ L), B ≤ E
    · obtain ⟨E, hE, hBE⟩ := hEx
      exact h65'.1 E hE hBE
    · push Not at hEx
      exact (h65'.2 hEx).2
  have hbD := hBD hbB
  obtain ⟨hLK, hKL⟩ := llRel_and_not_llRel_of_lt (isPerfect_of_mem_thetaComponentFamily hLA)
    hbD.2 (hAab.2 b hbD.1) hK hYK
  exact hKL (hL.2 K (mem_thetaComponentFamily_iff.mpr ⟨b, hbD.1, hb1, hK⟩) hLK)

theorem rank3II_6_8Used (h45 : Sec4.Item4_5) (h65 : Item6_5Used) (hKf : KFacts.KS6OuterIndex) :
    Item6_8 :=
  rank3II_6_8 h45 (rank3II_6_6Used h65) hKf

theorem rank3II_6_6_of_used (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9) :
    Item6_6 :=
  rank3II_6_6Used (rank3II_6_5Used h45 h48 h49)

theorem rank3II_6_8_of_used (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hKf : KFacts.KS6OuterIndex) : Item6_8 :=
  rank3II_6_8Used h45 (rank3II_6_5Used h45 h48 h49) hKf

end CFSG.RankThree.PartTwo.Sec6
