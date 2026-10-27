module

public import CFSG.Quasithin.Background.Basic
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem card_sup_mul_card_inf {H K : Subgroup G} (hKH : K ≤ Subgroup.normalizer (H : Set G)) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  set X := H ⊔ K
  have hHX : H ≤ X := le_sup_left
  have hKX : K ≤ X := le_sup_right
  have hN : (H.subgroupOf X).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hHX).mpr ?_
    exact sup_le Subgroup.le_normalizer hKH
  have h1 : (H.subgroupOf X).relIndex (K.subgroupOf X ⊔ H.subgroupOf X) =
      (H.subgroupOf X).relIndex (K.subgroupOf X) := Subgroup.relIndex_sup_right _ _
  have hsup : K.subgroupOf X ⊔ H.subgroupOf X = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hKX hHX, sup_comm]
    exact Subgroup.subgroupOf_self X
  rw [hsup, Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hKX] at h1
  have e1 := Subgroup.relIndex_mul_card H X
  have e2 := Subgroup.relIndex_mul_card H K
  rw [inf_of_le_left hHX] at e1
  have h1' : H.relIndex X = H.relIndex K := h1
  calc Nat.card ↥X * Nat.card ↥(H ⊓ K) = H.relIndex X * Nat.card H * Nat.card ↥(H ⊓ K) := by
        rw [e1]
    _ = Nat.card H * (H.relIndex K * Nat.card ↥(H ⊓ K)) := by rw [h1']; ring
    _ = Nat.card H * Nat.card K := by rw [e2]

theorem card_mul_le_of_isMaxElemAbelian {T A X : Subgroup G} (hA : IsMaxElemAbelian T A)
    (hX : IsElemAbelian 2 X) (hXT : X ≤ T) :
    Nat.card X * Nat.card ↥(A ⊓ Subgroup.centralizer (X : Set G)) ≤
      Nat.card A * Nat.card ↥(X ⊓ Subgroup.centralizer (A : Set G)) := by
  set A' := A ⊓ Subgroup.centralizer (X : Set G) with hA'
  have hcomm : ∀ a ∈ A', ∀ x ∈ X, a * x = x * a := fun a ha x hx =>
    (Subgroup.mem_centralizer_iff.mp ha.2 x hx).symm
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hX.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hA'X : A' ≤ Subgroup.normalizer (X : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hcomm a ha y hy, mul_inv_cancel_right]
      exact hy
    · intro hy
      have hai : a⁻¹ ∈ A' := A'.inv_mem ha
      have e : a⁻¹ * (a * y * a⁻¹) * a = a * y * a⁻¹ := by
        rw [hcomm a⁻¹ hai _ hy, inv_mul_cancel_right]
      have e2 : a⁻¹ * (a * y * a⁻¹) * a = y := by group
      rw [← e2, e]
      exact hy
  set B := A' ⊔ X with hB
  have hBc : ↑B = (A' : Set G) * (X : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A' X hA'X
  have hBel : IsElemAbelian 2 B := by
    have hmem : ∀ b ∈ B, ∃ a ∈ A', ∃ x ∈ X, b = a * x := by
      intro b hb
      have hb' : b ∈ (B : Set G) := hb
      rw [hBc] at hb'
      obtain ⟨a, ha, x, hx, rfl⟩ := hb'
      exact ⟨a, ha, x, hx, rfl⟩
    refine ⟨⟨⟨fun b₁ b₂ => Subtype.ext ?_⟩⟩, fun b hb => ?_⟩
    · obtain ⟨a₁, ha₁, x₁, hx₁, h₁⟩ := hmem b₁ b₁.2
      obtain ⟨a₂, ha₂, x₂, hx₂, h₂⟩ := hmem b₂ b₂.2
      simp only [Subgroup.coe_mul, h₁, h₂]
      have e1 : a₁ * x₁ * (a₂ * x₂) = (a₁ * a₂) * (x₁ * x₂) := by
        rw [mul_assoc, ← mul_assoc x₁, ← hcomm a₂ ha₂ x₁ hx₁]; group
      have e2 : a₂ * x₂ * (a₁ * x₁) = (a₂ * a₁) * (x₂ * x₁) := by
        rw [mul_assoc, ← mul_assoc x₂, ← hcomm a₁ ha₁ x₂ hx₂]; group
      rw [e1, e2, hAc a₁ ha₁.1 a₂ ha₂.1, hXc x₁ hx₁ x₂ hx₂]
    · obtain ⟨a, ha, x, hx, rfl⟩ := hmem b hb
      have e : (a * x) ^ 2 = a ^ 2 * x ^ 2 := by
        rw [pow_two, pow_two, pow_two, mul_assoc, ← mul_assoc x, ← hcomm a ha x hx]; group
      rw [e, hA.2.1.2 a ha.1, hX.2 x hx, one_mul]
  have hBT : B ≤ T := sup_le (inf_le_left.trans hA.1) hXT
  have hBA := hA.2.2 B hBT hBel
  have hcard := card_sup_mul_card_inf hA'X
  have hle : A' ⊓ X ≤ X ⊓ Subgroup.centralizer (A : Set G) := by
    rintro x ⟨⟨hxA, -⟩, hxX⟩
    exact ⟨hxX, Subgroup.mem_centralizer_iff.mpr fun a ha => hAc a ha x hxA⟩
  have hle' := Subgroup.card_le_of_le hle
  rw [sup_comm, inf_comm] at hcard
  calc Nat.card X * Nat.card A' = Nat.card B * Nat.card ↥(A' ⊓ X) := hcard.symm
    _ ≤ Nat.card A * Nat.card ↥(X ⊓ Subgroup.centralizer (A : Set G)) :=
      Nat.mul_le_mul hBA hle'

end CFSG.Quasithin.Vol2.Ch10.SecC
