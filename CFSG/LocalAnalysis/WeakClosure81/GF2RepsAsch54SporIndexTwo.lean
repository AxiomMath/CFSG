module

public import Mathlib.GroupTheory.Index

import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

variable {G : Type*} [Group G]

theorem conj_mem_of_forall_mem_closure {s : Set G} {t : G}
    (h : ∀ g ∈ s, t * g * t⁻¹ ∈ closure s) : ∀ x ∈ closure s, t * x * t⁻¹ ∈ closure s := by
  have hle : closure s ≤ (closure s).comap (MulAut.conj t).toMonoidHom := by
    rw [closure_le]
    intro g hg
    exact h g hg
  intro x hx
  exact hle hx

theorem mem_sup_zpowers_iff {X : Subgroup G} {t : G} (ht : t * t = 1)
    (hX : ∀ x ∈ X, t * x * t⁻¹ ∈ X) (y : G) : y ∈ X ⊔ zpowers t ↔ y ∈ X ∨ y * t ∈ X := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  let K : Subgroup G :=
    { carrier := {y | y ∈ X ∨ y * t ∈ X}
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (X.mul_mem hx hy)
        · right
          rw [mul_assoc]
          exact X.mul_mem hx hy
        · right
          have e : x * y * t = (x * t) * (t * y * t⁻¹) := by
            rw [hti]
            calc x * y * t = x * (t * t) * y * t := by rw [ht, mul_one]
              _ = (x * t) * (t * y * t) := by simp only [mul_assoc]
          rw [e]
          exact X.mul_mem hx (hX y hy)
        · left
          have e : x * y = (x * t) * (t * (y * t) * t⁻¹) := by
            rw [hti]
            calc x * y = x * (t * t) * y * (t * t) := by rw [ht, mul_one, mul_one]
              _ = (x * t) * (t * (y * t) * t) := by simp only [mul_assoc]
          rw [e]
          exact X.mul_mem hx (hX _ hy)
      one_mem' := Or.inl X.one_mem
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (X.inv_mem hx)
        · right
          have e : x⁻¹ * t = t * (x * t)⁻¹ * t⁻¹ := by
            rw [hti, mul_inv_rev, hti]
            calc x⁻¹ * t = (t * t) * x⁻¹ * t := by rw [ht, one_mul]
              _ = t * (t * x⁻¹) * t := by simp only [mul_assoc]
          rw [e]
          exact hX _ (X.inv_mem hx) }
  constructor
  · intro hy
    have hle : X ⊔ zpowers t ≤ K := by
      refine sup_le (fun x hx => Or.inl hx) ?_
      rw [zpowers_le]
      exact Or.inr (by rw [ht]; exact X.one_mem)
    exact hle hy
  · rintro (hy | hy)
    · exact mem_sup_left hy
    · have e : y = (y * t) * t⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
      rw [e]
      exact mul_mem (mem_sup_left hy) (mem_sup_right (inv_mem (mem_zpowers t)))

theorem card_sup_zpowers_eq_two_mul {X : Subgroup G} {t : G} (ht : t * t = 1) (htX : t ∉ X)
    (hX : ∀ x ∈ X, t * x * t⁻¹ ∈ X) : Nat.card ↥(X ⊔ zpowers t) = 2 * Nat.card ↥X := by
  set K := X ⊔ zpowers t with hK
  have hXK : X ≤ K := le_sup_left
  have htK : t ∈ K := mem_sup_right (mem_zpowers t)
  have hidx : (X.subgroupOf K).index = 2 := by
    rw [index_eq_two_iff]
    refine ⟨⟨t, htK⟩, fun b => ?_⟩
    simp only [mem_subgroupOf, coe_mul]
    rcases (mem_sup_zpowers_iff ht hX b).1 b.2 with hb | hb
    · refine Or.inr ⟨hb, fun hbt => htX ?_⟩
      have e : t = (b : G)⁻¹ * (b * t) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      rw [e]
      exact X.mul_mem (X.inv_mem hb) hbt
    · refine Or.inl ⟨hb, fun hb' => htX ?_⟩
      have e : t = (b : G)⁻¹ * (b * t) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      rw [e]
      exact X.mul_mem (X.inv_mem hb') hb
  rw [← (X.subgroupOf K).card_mul_index, hidx, Nat.card_congr (subgroupOfEquivOfLe hXK).toEquiv,
    mul_comm]

theorem eq_top_of_index_eq_two {M K : Subgroup G} (hM : M.index = 2) (hle : M ≤ K) {t : G}
    (htK : t ∈ K) (htM : t ∉ M) : K = ⊤ := by
  rw [eq_top_iff]
  intro y _
  rcases (index_eq_two_iff.1 hM) with ⟨a, ha⟩
  have hdich : ∀ b : G, b ∈ M ∨ b * a ∈ M := fun b => by
    rcases ha b with h | h
    · exact Or.inr h.1
    · exact Or.inl h.1
  have hta : t * a ∈ M := (hdich t).resolve_left htM
  rcases hdich y with hy | hy
  · exact hle hy
  · have e : y = (y * a) * (t * a)⁻¹ * t := by group
    rw [e]
    exact K.mul_mem (K.mul_mem (hle hy) (K.inv_mem (hle hta))) htK

end CFSG.LocalAnalysis.WeakClosure81

end
