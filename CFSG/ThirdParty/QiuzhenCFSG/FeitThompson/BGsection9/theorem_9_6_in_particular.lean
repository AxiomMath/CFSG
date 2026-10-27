module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection9.theorem_9_6
import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.Subgroup.Centralizer

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Theorem 9.6 in particular from BG Section 9

This file contains the final "in particular" statement of Theorem 9.6 from `docs/section9.tex`.
-/

section Section9

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

private theorem CFSG.section9_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq
    {p : ℕ} [Fact p.Prime] {A : Type*} [Group A] [Finite A]
    [IsElementaryAbelian p A] (hA : Nat.card A = p ^ 2) :
    2 ≤ generatorRank A := by
  letI : CommGroup A := IsMulCommutative.instCommGroup
  have hcard_dvd : Nat.card A ∣ p ^ Group.rank A := by
    simpa using card_dvd_exponent_pow_rank' (G := A) (n := p) (fun a =>
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (show Monoid.exponent A ∣ p by simpa using IsElementaryAbelian.exponent_dvd_p p A) a)
  rw [hA] at hcard_dvd
  have hle_rank : 2 ≤ Group.rank A := by
    exact (Nat.pow_dvd_pow_iff_le_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hcard_dvd
  simpa [generatorRank_eq_group_rank] using hle_rank

private theorem CFSG.section9_groupRank_at_least_two_of_elementaryAbelian_card_p_sq
    {p : ℕ} [Fact p.Prime] {A : Type*} [Group A] [Finite A]
    [IsElementaryAbelian p A] (hA : Nat.card A = p ^ 2) :
    2 ≤ groupRank A := by
  have hgen : 2 ≤ generatorRank A :=
    section9_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq (p := p) hA
  have htop_p : IsPGroup p (⊤ : Subgroup A) := by
    simpa using (IsElementaryAbelian.isPGroup p A).to_subgroup (⊤ : Subgroup A)
  have htop_comm : IsMulCommutative (⊤ : Subgroup A) := by
    infer_instance
  have htop_gen : 2 ≤ generatorRank (⊤ : Subgroup A) := by
    have htop_gen_eq : generatorRank (⊤ : Subgroup A) = generatorRank A := by
      rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
      exact Group.rank_congr Subgroup.topEquiv
    simpa [htop_gen_eq] using hgen
  have hp_rank : 2 ≤ primeRank p A := by
    rw [primeRank]
    refine le_csSup ?_ ?_
    · refine ⟨Nat.card A, ?_⟩
      intro n hn
      rcases hn with ⟨B, _hBp, _hBcomm, hnB⟩
      exact hnB.trans <|
        (generatorRank_le_natCard B).trans (Subgroup.card_le_card_group B)
    · exact ⟨⊤, htop_p, htop_comm, htop_gen⟩
  rw [groupRank]
  refine le_csSup ?_ ?_
  · refine ⟨Nat.card A, ?_⟩
    intro n hn
    rcases hn with ⟨q, _hq, hnq⟩
    exact hnq.trans (primeRank_le_natCard (p := q) A)
  · exact ⟨p, Fact.out, hp_rank⟩

private theorem CFSG.section9_generatorRank_at_least_three_of_elementaryAbelian_card_gt_p_sq
    {p : ℕ} [Fact p.Prime] {A : Type*} [Group A] [Finite A]
    [IsElementaryAbelian p A] (hgt : p ^ 2 < Nat.card A) :
    3 ≤ generatorRank A := by
  letI : CommGroup A := IsMulCommutative.instCommGroup
  have hcard_dvd : Nat.card A ∣ p ^ Group.rank A := by
    simpa using card_dvd_exponent_pow_rank' (G := A) (n := p) (fun a =>
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (show Monoid.exponent A ∣ p by simpa using IsElementaryAbelian.exponent_dvd_p p A) a)
  have hnot_le_two : ¬ Group.rank A ≤ 2 := by
    intro hle_two
    have hcard_le : Nat.card A ≤ p ^ Group.rank A :=
      Nat.le_of_dvd (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) _) hcard_dvd
    have hpow_le : p ^ Group.rank A ≤ p ^ 2 :=
      Nat.pow_le_pow_right (Nat.Prime.pos (Fact.out : Nat.Prime p)) hle_two
    exact (not_lt_of_ge (hcard_le.trans hpow_le)) hgt
  have hle_rank : 3 ≤ Group.rank A := by omega
  simpa [generatorRank_eq_group_rank] using hle_rank

/-- The final "in particular" statement of Theorem 9.6. -/
public theorem CFSG.theorem_9_6_in_particular
    {A : Subgroup G} (hA : section9RankTwoNonmaximalElementaryAbelian A) :
    A ∈ section9UniqueSubgroups G := by
  rcases hA with ⟨p, hp, hArankTwo, hAnonmax⟩
  letI : Fact p.Prime := ⟨hp⟩
  rcases hArankTwo with ⟨hAcard, hAelem⟩
  letI : IsElementaryAbelian p A := hAelem
  have hAproper : A ≠ ⊤ := by
    intro hAtop
    apply hAnonmax
    refine ⟨hAelem, ?_⟩
    intro B hAB _hBelem
    rw [hAtop] at hAB ⊢
    exact le_antisymm hAB le_top
  have hAgroupRank : 2 ≤ groupRank A :=
    section9_groupRank_at_least_two_of_elementaryAbelian_card_p_sq (p := p) hAcard
  have hExistsOver :
      ∃ B : Subgroup G, A ≤ B ∧ IsElementaryAbelian p B ∧ A ≠ B := by
    by_contra hnone
    apply hAnonmax
    refine ⟨hAelem, ?_⟩
    intro B hAB hBelem
    by_contra hABne
    exact hnone ⟨B, hAB, hBelem, hABne⟩
  rcases hExistsOver with ⟨B, hAB, hBelem, hABne⟩
  have hAltB : A < B := lt_of_le_of_ne hAB hABne
  have hBcard_gt : p ^ 2 < Nat.card B := by
    simpa [hAcard] using natCard_lt_of_subgroup_lt hAltB
  letI : IsElementaryAbelian p B := hBelem
  have hBgen : 3 ≤ generatorRank B :=
    section9_generatorRank_at_least_three_of_elementaryAbelian_card_gt_p_sq (p := p) hBcard_gt
  have hB_le_centralizer : B ≤ Subgroup.centralizer (A : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact setLike_mul_comm (s := B) (hAB ha) hb
  have hcentralizerRank : 3 ≤ groupRank (Subgroup.centralizer (A : Set G)) := by
    exact groupRank_at_least_three_of_generatorRank_subgroup
      (q := p) hp hB_le_centralizer (IsElementaryAbelian.isPGroup p B)
      (inferInstance : IsMulCommutative B) hBgen
  exact theorem_9_6 (K := A) hAproper hAgroupRank (Or.inr hcentralizerRank)

end Section9
