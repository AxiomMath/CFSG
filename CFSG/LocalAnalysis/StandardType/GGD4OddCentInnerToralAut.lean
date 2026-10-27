module

public import CFSG.LocalAnalysis.StandardType.GGHypSixD4BstarRankTri
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45RankXTriality

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.Triality

namespace D4Inner

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem isTriPart_zero_iff_mem_sup {a : MulAut (Om8 K)} :
    D4Bstar.IsTriPart 0 a ↔ a ∈ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range := by
  constructor
  · rintro ⟨γ, σ, rfl⟩
    rw [pow_zero, one_mul]
    exact Subgroup.mul_mem_sup ⟨γ, rfl⟩ ⟨σ, rfl⟩
  · intro h
    obtain ⟨ι, ⟨γ, rfl⟩, _, ⟨σ, rfl⟩, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 h
    exact ⟨γ, σ, by rw [pow_zero, one_mul]⟩

theorem exists_isTriPart_lt_three {a : MulAut (Om8 K)} (ha : a ^ 3 = 1) :
    ∃ k < 3, D4Bstar.IsTriPart k a := by
  by_cases h : a ∈ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range
  · exact ⟨0, by norm_num, isTriPart_zero_iff_mem_sup.2 h⟩
  · obtain ⟨γ, k, σ, hk, rfl⟩ :=
      L45RankX.exists_conj_theta_pow_fieldAutP_of_pow (e := 1) (by rwa [pow_one]) h
    exact ⟨k, by omega, γ, σ, rfl⟩

theorem exists_isTriPart_of_not_mem {α : MulAut (Om8 K)} (hα3 : α ^ 3 = 1)
    (hα : α ∉ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range) :
    ∃ k, (k = 1 ∨ k = 2) ∧ D4Bstar.IsTriPart k α := by
  obtain ⟨γ, k, σ, hk, rfl⟩ :=
    L45RankX.exists_conj_theta_pow_fieldAutP_of_pow (e := 1) (by rwa [pow_one]) hα
  exact ⟨k, hk, γ, σ, rfl⟩

theorem exists_mul_pow_mem_inner {A : Subgroup (MulAut (Om8 K))} (hA : IsElemAbelian 3 A)
    (hdat : ∀ a ∈ A, a ∈ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range → a ∈ Inn (Om8 K))
    {α : MulAut (Om8 K)} (hαA : α ∈ A) (hα : α ∉ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range)
    {a : MulAut (Om8 K)} (ha : a ∈ A) : ∃ j < 3, a * α ^ j ∈ Inn (Om8 K) := by
  obtain ⟨k₀, hk₀, h₀⟩ := exists_isTriPart_of_not_mem (hA.2 α hαA) hα
  obtain ⟨k, hk, hka⟩ := exists_isTriPart_lt_three (hA.2 a ha)
  obtain ⟨j, hj, hjk⟩ : ∃ j < 3, (k + j * k₀) % 3 = 0 := by
    rcases hk₀ with rfl | rfl <;> interval_cases k
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨2, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩
    · exact ⟨2, by norm_num, rfl⟩
  refine ⟨j, hj, hdat _ (A.mul_mem ha (A.pow_mem hαA j)) ?_⟩
  have h := (hka.mul (h₀.pow j)).mod_three
  rw [hjk] at h
  exact isTriPart_zero_iff_mem_sup.1 h

theorem nine_le_card_inf_inner {A : Subgroup (MulAut (Om8 K))} (hA : IsElemAbelian 3 A)
    (hcard : Nat.card A = 3 ^ 3)
    (hdat : ∀ a ∈ A, a ∈ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range → a ∈ Inn (Om8 K))
    {α : MulAut (Om8 K)} (hαA : α ∈ A) (hα : α ∉ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range) :
    3 ^ 2 ≤ Nat.card ↥(A ⊓ Inn (Om8 K)) := by
  set H : Subgroup A := (Inn (Om8 K)).subgroupOf A with hH
  have hcomm : ∀ a b : A, a * b = b * a := fun a b => hA.1.is_comm.comm a b
  have hsurj : Function.Surjective fun j : Fin 3 =>
      (QuotientGroup.mk ((⟨α, hαA⟩ : A) ^ (2 * (j : ℕ))) : A ⧸ H) := by
    refine fun q => Quotient.inductionOn' q fun a => ?_
    obtain ⟨j, hj, hmem⟩ := exists_mul_pow_mem_inner hA hdat hαA hα a.2
    refine ⟨⟨j, hj⟩, (QuotientGroup.eq.2 ?_).symm⟩
    have hα3 : (⟨α, hαA⟩ : A) ^ 3 = 1 := Subtype.ext (by simpa using hA.2 α hαA)
    have hmem' : a * (⟨α, hαA⟩ : A) ^ j ∈ H := by
      rw [hH, Subgroup.mem_subgroupOf]; simpa using hmem
    have h2 : a⁻¹ * (⟨α, hαA⟩ : A) ^ (2 * j) = (a * (⟨α, hαA⟩ : A) ^ j)⁻¹ := by
      rw [mul_inv_rev, hcomm _ a⁻¹]
      congr 1
      rw [← mul_left_inj ((⟨α, hαA⟩ : A) ^ j), inv_mul_cancel, ← pow_add,
        show 2 * j + j = 3 * j by ring, pow_mul, hα3, one_pow]
    rw [h2]
    exact H.inv_mem hmem'
  have hidx : H.index ≤ 3 := by
    rw [Subgroup.index]
    simpa using Nat.card_le_card_of_surjective _ hsurj
  have hmul := Subgroup.card_mul_index H
  rw [hcard] at hmul
  have hHcard : Nat.card H = Nat.card ↥(A ⊓ Inn (Om8 K)) := by
    rw [inf_comm, ← Subgroup.subgroupOf_map_subtype,
      Subgroup.card_map_of_injective A.subtype_injective]
  rw [← hHcard]
  by_contra hlt
  push Not at hlt
  have : Nat.card H * H.index < 3 ^ 3 := by
    calc Nat.card H * H.index ≤ Nat.card H * 3 := Nat.mul_le_mul_left _ hidx
      _ < 3 ^ 2 * 3 := by
        have : 0 < 3 := by norm_num
        exact (Nat.mul_lt_mul_right this).2 hlt
      _ = 3 ^ 3 := by norm_num
  omega

end D4Inner

end CFSG.StandardType

end
