module

public import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec6.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

variable {G : Type} [Group G] [Finite G]

theorem llRel_and_not_llRel_of_lt {b : G} {L K : Subgroup G} (hLp : Group.IsPerfect L)
    (hb : b ∈ thetaQuotCentralizer L) (hb3 : b ^ 3 = 1) (hK : K ∈ thetaComponentsAt 3 b)
    (hYK : inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {b}) ⊔
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {b})) < K) :
    llRel L K ∧ ¬ llRel K L := by
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  set H := Subgroup.centralizer ({b} : Set G) with hH
  set M := L ⊓ H with hM
  set W := M ⊔ inSubgroup (aschbacherSolvableCore 3) H with hW
  have hKp := isPerfect_of_mem_thetaComponentsAt hK
  have hKH := le_centralizer_of_mem_thetaComponentsAt hK
  have hLcov := le_inf_centralizer_sup_theta hb hb3
  have hLM : L ≤ inSubgroup perfectResidual M ⊔ θL :=
    le_perfectResidual_sup hLp (inf_le_left.trans (le_normalizer_theta L)) hLcov
  have hMK : inSubgroup perfectResidual M ≤ K :=
    (inSubgroup_perfectResidual_mono le_sup_left).trans hYK.le
  have hMLK : inSubgroup perfectResidual M ≤ inSubgroup perfectResidual (L ⊓ K) :=
    le_inSubgroup_perfectResidual_of_isPerfect (isPerfect_inSubgroup_perfectResidual M)
      (le_inf ((Subgroup.map_subtype_le _).trans inf_le_left) hMK)
  refine ⟨le_antisymm (hLM.trans (sup_le_sup_right hMLK θL))
    (sup_le ((Subgroup.map_subtype_le _).trans inf_le_left) (theta_le L)), fun hKL => ?_⟩
  have hKW : K ≤ W := by
    rw [hKL]
    refine sup_le ((Subgroup.map_subtype_le _).trans ?_) ?_
    · exact (le_inf inf_le_right (inf_le_left.trans hKH)).trans le_sup_left
    · rw [theta_eq_inf_of_mem_thetaComponentsAt hK]
      exact inf_le_right.trans le_sup_right
  exact (lt_irrefl K) (lt_of_le_of_lt (le_inSubgroup_perfectResidual_of_isPerfect hKp hKW) hYK)

theorem rank3II_6_6 (h65 : Item6_5) : Item6_6 := by
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
      obtain ⟨b, hb, hb1, K, hK, hY, -⟩ := h65'.1 E hE hBE
      exact ⟨b, hb, hb1, K, hK, hY⟩
    · push Not at hEx
      obtain ⟨-, b, hb, hb1, K, hK, hY⟩ := h65'.2 hEx
      exact ⟨b, hb, hb1, K, hK, hY⟩
  have hbD := hBD hbB
  obtain ⟨hLK, hKL⟩ := llRel_and_not_llRel_of_lt (isPerfect_of_mem_thetaComponentFamily hLA)
    hbD.2 (hAab.2 b hbD.1) hK hYK
  exact hKL (hL.2 K (mem_thetaComponentFamily_iff.mpr ⟨b, hbD.1, hb1, hK⟩) hLK)

end CFSG.RankThree.PartTwo.Sec6
