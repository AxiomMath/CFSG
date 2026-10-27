module

public import CFSG.Sporadic.SmallOddCore.Co3Classes
public import CFSG.Sporadic.Schreier.Co3FirstAut
public import CFSG.ClassicalGroups.Symplectic.Simple

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.Schreier CFSG.Blueprint
open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Symplectic

theorem oddCore_eq_bot_of_surj {K Q : Type*} [Group K] [Group Q] [Finite K] [IsSimpleGroup Q]
    (φ : K →* Q) (hφ : Function.Surjective φ) (hker : Nat.card φ.ker = 2)
    (heven : Even (Nat.card Q)) : CFSG.oddCore K = ⊥ := by
  have hOodd : Odd (Nat.card (CFSG.oddCore K)) :=
    CFSG.ComponentClassification.SmallLocal.odd_card_oddCore
  have hOn : (CFSG.oddCore K).Normal := CFSG.oddCore_normal K
  have := hOn.map φ hφ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.oddCore K).map φ) with h | h
  · have hle : CFSG.oddCore K ≤ φ.ker := (Subgroup.map_eq_bot_iff _).mp h
    have hdvd : Nat.card (CFSG.oddCore K) ∣ 2 := hker ▸ Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact Subgroup.card_eq_one.mp h1
    · rw [h2] at hOodd
      exact absurd hOodd (by decide)
  · exfalso
    have h1 := Subgroup.card_map_dvd (CFSG.oddCore K) φ
    rw [h, Subgroup.card_top] at h1
    exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hOodd h1)) heven

theorem co3M_oddCore : CFSG.oddCore co3M = ⊥ := by
  have : IsSimpleGroup (StatedProj (StatedSp 3 (ZMod 2))) :=
    isSimpleGroup_statedProj_statedSp (ZMod 2) 3 (by norm_num)
      (Or.inr (Or.inr ⟨by simp, by norm_num⟩))
  have : IsSimpleGroup (co3M ⧸ Subgroup.center co3M) := co3MQuotProj.isSimpleGroup
  have hcard := (Subgroup.center co3M).card_eq_card_quotient_mul_card_subgroup
  rw [card_co3M, card_co3M_center] at hcard
  refine oddCore_eq_bot_of_surj (QuotientGroup.mk' (Subgroup.center co3M))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact card_co3M_center) ?_
  refine ⟨Nat.card (co3M ⧸ Subgroup.center co3M) / 2, ?_⟩
  omega

theorem co3M1_oddCore : CFSG.oddCore co3M1 = ⊥ := by
  have : IsSimpleGroup ↥co3Kappa1.range := by
    rw [co3Kappa1_range]
    exact CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  refine oddCore_eq_bot_of_surj co3Kappa1.rangeRestrict co3Kappa1.rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict]; exact card_ker_co3Kappa1) ?_
  rw [co3Kappa1_range, m12_card]
  decide

theorem ctuc_co3_involution_centralizers_odd_core_trivial :
    ∀ u ∈ co3P, orderOf u = 2 →
      CFSG.oddCore ↥(co3P ⊓ centralizer ({u} : Set (Equiv.Perm (Fin 276)))) = ⊥ := by
  intro u hu hu2
  have hz : CFSG.oddCore ↥(co3P ⊓ centralizer ({co3Z} : Set (Equiv.Perm (Fin 276)))) = ⊥ :=
    co3M_eq_centralizer ▸ co3M_oddCore
  have ht : CFSG.oddCore ↥(co3P ⊓ centralizer ({co3Tt} : Set (Equiv.Perm (Fin 276)))) = ⊥ :=
    co3M1_eq_centralizer ▸ co3M1_oddCore
  obtain ⟨-, -, -, hcl, -, -⟩ := ctuc_co3_complete_inner_involution_classes
  by_cases h : ∃ g ∈ co3P, u = g * co3Z * g⁻¹
  · obtain ⟨g, hg, rfl⟩ := h
    exact oddCore_inf_centralizer_conj co3P hg hz
  · have h' : ∃ g ∈ co3P, u = g * co3Tt * g⁻¹ := by
      by_contra h''
      exact h ((hcl u hu hu2).2 h'')
    obtain ⟨g, hg, rfl⟩ := h'
    exact oddCore_inf_centralizer_conj co3P hg ht

end CFSG.Sporadic.SmallOddCore
