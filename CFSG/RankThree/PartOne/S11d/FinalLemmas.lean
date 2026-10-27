module

public import CFSG.GroupTheory.ABGLocalTools.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartOne

open Subgroup
open scoped Pointwise

theorem exists_isSylowOf_ge {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {K Q : Subgroup G} (hQK : Q ≤ K) (hQ : IsPGroup p Q) :
    ∃ T : Subgroup G, ABGLocalTools.IsSylowOf p T K ∧ Q ≤ T := by
  obtain ⟨S, hS⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(S : Subgroup K).map K.subtype, ⟨S, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hQK hx⟩, hS hx, rfl⟩

theorem exists_conj_mem_of_isSylowOf {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {K T : Subgroup G} (hT : ABGLocalTools.IsSylowOf p T K) {g : G} (hg : g ∈ K)
    (hgp : ∃ k : ℕ, orderOf g = p ^ k) : ∃ h ∈ K, h * g * h⁻¹ ∈ T := by
  obtain ⟨S, rfl⟩ := hT
  obtain ⟨k, hk⟩ := hgp
  have hZ : IsPGroup p (zpowers (⟨g, hg⟩ : K)) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hk])
  obtain ⟨S', hS'⟩ := hZ.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq K S' S
  have hmem : n * ⟨g, hg⟩ * n⁻¹ ∈ (S : Subgroup K) := by
    rw [← hn, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hS' (mem_zpowers _))
  exact ⟨n, n.2, ⟨_, hmem, rfl⟩⟩

theorem exists_proportional {p : ℕ} (hp : p.Prime) (α β α' β' : ℤ)
    (h : ¬ ((p : ℤ) ∣ α ∧ (p : ℤ) ∣ β)) (hdet : (p : ℤ) ∣ α' * β - β' * α) :
    ∃ m : ℤ, (p : ℤ) ∣ α' - m * α ∧ (p : ℤ) ∣ β' - m * β := by
  have := Fact.mk hp
  have hdet' : (α' : ZMod p) * β - β' * α = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (α' * β - β' * α) p).mpr hdet
    simpa using this
  by_cases hα : (α : ZMod p) = 0
  · have hβ : (β : ZMod p) ≠ 0 := fun hβ0 =>
      h ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd α p).mp hα,
        (ZMod.intCast_zmod_eq_zero_iff_dvd β p).mp hβ0⟩
    obtain ⟨m, hm⟩ := ZMod.intCast_surjective ((β' : ZMod p) / (β : ZMod p))
    have hα' : (α' : ZMod p) = 0 := by
      rw [hα, mul_zero, sub_zero] at hdet'
      exact (mul_eq_zero.mp hdet').resolve_right hβ
    refine ⟨m, ?_, ?_⟩
    · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hα, hα']
      ring
    · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hm]
      field_simp
      ring
  · obtain ⟨m, hm⟩ := ZMod.intCast_surjective ((α' : ZMod p) / (α : ZMod p))
    refine ⟨m, ?_, ?_⟩
    · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hm]
      field_simp
      ring
    · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hm]
      field_simp
      linear_combination -hdet'

theorem exponent_sup_zpowers {G : Type*} [Group G] {p : ℕ}
    {A : Subgroup G} (hA : ∀ x ∈ A, x ^ p = 1)
    {ζ : G} (hζ : ζ ∈ Subgroup.centralizer (A : Set G)) (hpζ : p ∣ orderOf ζ) :
    Monoid.exponent ↥(A ⊔ Subgroup.zpowers ζ) = orderOf ζ := by
  have hmul : ((A ⊔ zpowers ζ : Subgroup G) : Set G) = (A : Set G) * (zpowers ζ : Set G) :=
    coe_mul_of_right_le_normalizer_left A (zpowers ζ)
      (zpowers_le.mpr (centralizer_le_normalizer _ hζ))
  have key : ∀ g ∈ A ⊔ zpowers ζ, g ^ orderOf ζ = 1 := by
    intro g hg
    rw [← SetLike.mem_coe, hmul] at hg
    obtain ⟨β, hβ, z, hz, rfl⟩ := hg
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hz
    have hcomm : Commute β (ζ ^ j) :=
      (show Commute β ζ from mem_centralizer_iff.mp hζ β hβ).zpow_right j
    obtain ⟨c, hc⟩ := hpζ
    have hβn : β ^ orderOf ζ = 1 := by rw [hc, pow_mul, hA β hβ, one_pow]
    have hζn : (ζ ^ j) ^ orderOf ζ = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
        one_zpow]
    rw [hcomm.mul_pow, hβn, hζn, one_mul]
  refine Nat.dvd_antisymm (Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_) ?_
  · exact Subtype.ext (key x.1 x.2)
  · have := Monoid.order_dvd_exponent
      (⟨ζ, mem_sup_right (mem_zpowers ζ)⟩ : ↥(A ⊔ zpowers ζ))
    rwa [Subgroup.orderOf_mk] at this

end CFSG.RankThree.PartOne
