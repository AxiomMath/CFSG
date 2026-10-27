module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Frattini

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup
open scoped IsMulCommutative commutatorElement

variable {Q : Type*} [Group Q]

theorem commutator_mul_central_gc {z₁ z₂ : Q} (hz₁ : z₁ ∈ Subgroup.center Q)
    (hz₂ : z₂ ∈ Subgroup.center Q) (a b : Q) : ⁅a * z₁, b * z₂⁆ = ⁅a, b⁆ := by
  have c1 := Subgroup.mem_center_iff.1 hz₁
  have c2 := Subgroup.mem_center_iff.1 hz₂
  have h1 : ∀ g : Q, z₁ * g * z₁⁻¹ = g := fun g => by rw [← c1 g, mul_inv_cancel_right]
  have h2 : ∀ g : Q, z₂ * g * z₂⁻¹ = g := fun g => by rw [← c2 g, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  have e1 : (a * z₁) * (b * z₂) * (a * z₁)⁻¹ = a * (b * z₂) * a⁻¹ := by
    calc (a * z₁) * (b * z₂) * (a * z₁)⁻¹
        = a * (z₁ * (b * z₂) * z₁⁻¹) * a⁻¹ := by group
      _ = a * (b * z₂) * a⁻¹ := by rw [h1]
  have e2 : a * (b * z₂) * a⁻¹ * (b * z₂)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
    calc a * (b * z₂) * a⁻¹ * (b * z₂)⁻¹
        = a * b * (z₂ * a⁻¹ * z₂⁻¹) * b⁻¹ := by group
      _ = a * b * a⁻¹ * b⁻¹ := by rw [h2]
  rw [e1, e2]

theorem eq_top_of_sup_le_center_gc (hperf : Group.IsPerfect Q) {N Z : Subgroup Q}
    (hZ : Z ≤ Subgroup.center Q) (h : N ⊔ Z = ⊤) : N = ⊤ := by
  have : Z.Normal := Subgroup.normal_of_le_center hZ
  have hcomm : ∀ x y : Q, ⁅x, y⁆ ∈ N := by
    intro x y
    have hx : x ∈ N ⊔ Z := h ▸ Subgroup.mem_top x
    have hy : y ∈ N ⊔ Z := h ▸ Subgroup.mem_top y
    obtain ⟨n₁, hn₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
    obtain ⟨n₂, hn₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hy
    have key : ⁅n₁ * z₁, n₂ * z₂⁆ = ⁅n₁, n₂⁆ := commutator_mul_central_gc (hZ hz₁) (hZ hz₂) n₁ n₂
    rw [key, commutatorElement_def]
    exact N.mul_mem (N.mul_mem (N.mul_mem hn₁ hn₂) (N.inv_mem hn₁)) (N.inv_mem hn₂)
  have hle : commutator Q ≤ N := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact hcomm x y
  rw [Group.isPerfect_def.1 hperf] at hle
  exact top_le_iff.1 hle

theorem center_le_frattini_gc (hperf : Group.IsPerfect Q) {z : Q}
    (hz : z ∈ Subgroup.center Q) : z ∈ frattini Q := by
  rw [frattini, Order.radical]
  simp only [Subgroup.mem_iInf]
  intro M hM
  by_contra hzM
  have hsup : M ⊔ Subgroup.zpowers z = ⊤ := by
    refine hM.2 (M ⊔ Subgroup.zpowers z) ?_
    exact lt_of_le_of_ne le_sup_left (fun h => hzM
      (h ▸ (le_sup_right : zpowers z ≤ M ⊔ zpowers z) (Subgroup.mem_zpowers z)))
  have hZ : Subgroup.zpowers z ≤ Subgroup.center Q := by
    rw [Subgroup.zpowers_le]
    exact hz
  exact hM.1 (eq_top_of_sup_le_center_gc hperf hZ hsup)

theorem no_abelian_of_perfect_central_gc [Finite Q] (hperf : Group.IsPerfect Q) {S : Subgroup Q}
    (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {z : Q} (hz : z ∈ Subgroup.center Q)
    (h3 : orderOf z = 3) (hidx : ¬ 3 ∣ S.index) : False := by
  have : IsMulCommutative S := ⟨⟨fun a b => Subtype.ext (hS a a.2 b b.2)⟩⟩
  have : S.FiniteIndex := Subgroup.finiteIndex_of_finite
  have key : ∀ (k : ℕ) (g₀ : Q), g₀⁻¹ * z ^ k * g₀ ∈ S → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hc : z ^ k ∈ Subgroup.center Q := Subgroup.pow_mem _ hz k
    rw [Subgroup.mem_center_iff] at hc
    rw [hc g₀⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  have h1 := MonoidHom.transfer_eq_pow (MonoidHom.id S) z key
  have h2 : MonoidHom.transfer (MonoidHom.id S) z = 1 := by
    have hle : commutator Q ≤ (MonoidHom.transfer (MonoidHom.id S)).ker :=
      Abelianization.commutator_subset_ker _
    rw [Group.isPerfect_def.1 hperf] at hle
    exact hle (Subgroup.mem_top z)
  rw [h2] at h1
  have h3' : z ^ S.index = 1 := by
    have := congrArg Subtype.val h1.symm
    simpa using this
  exact hidx (h3 ▸ orderOf_dvd_of_pow_eq_one h3')

end CFSG.Quasithin.H13.U3.GC137
