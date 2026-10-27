module

public import CFSG.LocalAnalysis.SteinbergBNFirstTransferData
public import CFSG.CharacterTheory.Semidihedral.Local.PowerFusionTransfer
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.LocalAnalysis

open scoped IsMulCommutative

theorem perfect_first_transfer_exclusion {G : Type*} [Group G] [Finite G] [Group.IsPerfect G] :
    ¬∃ (S N : Subgroup G) (x : G), FirstTransferData S N x := by
  rintro ⟨S, N, x, ⟨P, rfl⟩, -, hnorm, hcomm, hx, hxN, hx2, hfus⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxN' : (⟨x, hx⟩ : P) ∉ N.subgroupOf (P : Subgroup G) := by
    rw [Subgroup.mem_subgroupOf]
    exact hxN
  have hpow : ∀ k : ℕ, x ^ k = 1 ∨ x ^ k = x := fun k => by
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · left
      rw [← two_mul, pow_mul, ← hx2, pow_orderOf_eq_one, one_pow]
    · right
      rw [pow_add, pow_mul, ← hx2, pow_orderOf_eq_one, one_pow, one_mul, pow_one]
  have hfus' : ∀ (k : ℕ) (g : G) (h : g⁻¹ * ((⟨x, hx⟩ : P) : G) ^ k * g ∈ (P : Subgroup G)),
      (QuotientGroup.mk' (N.subgroupOf (P : Subgroup G))
          ⟨g⁻¹ * ((⟨x, hx⟩ : P) : G) ^ k * g, h⟩ : P ⧸ N.subgroupOf (P : Subgroup G)) =
        QuotientGroup.mk' (N.subgroupOf (P : Subgroup G)) ((⟨x, hx⟩ : P) ^ k) := by
    intro k g h
    rcases hpow k with h1 | h1
    · have e1 : (⟨g⁻¹ * ((⟨x, hx⟩ : P) : G) ^ k * g, h⟩ : P) = 1 :=
        Subtype.ext (by simp only [h1, mul_one, inv_mul_cancel, OneMemClass.coe_one])
      have e2 : (⟨x, hx⟩ : P) ^ k = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow, h1]; rfl)
      rw [e1, e2]
    · have hg : g⁻¹ * x * g ∈ (P : Subgroup G) := by
        have h' := h
        simp only [h1] at h'
        exact h'
      have e1 : (⟨g⁻¹ * ((⟨x, hx⟩ : P) : G) ^ k * g, h⟩ : P) = ⟨g⁻¹ * x * g, hg⟩ :=
        Subtype.ext (by simp only [h1])
      have e2 : (⟨x, hx⟩ : P) ^ k = ⟨x, hx⟩ := Subtype.ext (by rw [SubgroupClass.coe_pow, h1])
      rw [e1, e2]
      exact hfus g hg
  obtain ⟨-, -, -, hxK, -⟩ :=
    CFSG.Semidihedral.Local.power_fusion_transfer_detection P (N.subgroupOf (P : Subgroup G))
      ⟨x, hx⟩ hxN' hfus'
  apply hxK
  have hle : commutator G ≤ ((QuotientGroup.mk' (N.subgroupOf (P : Subgroup G))).transfer :
      G →* P ⧸ N.subgroupOf (P : Subgroup G)).ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.is_comm.comm _ _
  exact hle (by rw [Group.IsPerfect.commutator_eq_top]; exact Subgroup.mem_top x)

end CFSG.LocalAnalysis
