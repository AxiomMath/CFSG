module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.Quasithin

section Dihedral

variable {H : Type*} [Group H] {s t : H}

theorem inv_eq_self_of_mul_self (hs : s * s = 1) : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs

theorem s_mul_zpow (hs : s * s = 1) (ht : t * t = 1) (j : ℤ) :
    s * (t * s) ^ j = (t * s) ^ (-j) * s := by
  have h1 : s * (t * s) * s⁻¹ = (t * s)⁻¹ := by
    rw [← mul_assoc, mul_inv_cancel_right, mul_inv_rev, inv_eq_self_of_mul_self hs,
      inv_eq_self_of_mul_self ht]
  have h2 : s * (t * s) ^ j * s⁻¹ = (t * s) ^ (-j) := by
    rw [← conj_zpow, h1, inv_zpow']
  rw [← h2, inv_mul_cancel_right]

theorem inv_rot_eq (hs : s * s = 1) (ht : t * t = 1) : (t * s)⁻¹ = s * t := by
  rw [mul_inv_rev, inv_eq_self_of_mul_self hs, inv_eq_self_of_mul_self ht]

theorem rot_pow_eq_inv (hs : s * s = 1) (ht : t * t = 1) (n : ℕ) :
    (t * s) ^ n = ((s * t) ^ n)⁻¹ := by
  rw [← inv_pow, mul_inv_rev, inv_eq_self_of_mul_self hs, inv_eq_self_of_mul_self ht]

theorem t_mul_zpow (hs : s * s = 1) (ht : t * t = 1) (j : ℤ) :
    t * (t * s) ^ j = (t * s) ^ (-j) * t := by
  have h1 : t * (t * s) * t⁻¹ = (t * s)⁻¹ := by
    rw [inv_eq_self_of_mul_self ht, ← mul_assoc, ht, one_mul,
      mul_inv_rev, inv_eq_self_of_mul_self hs, inv_eq_self_of_mul_self ht]
  have h2 : t * (t * s) ^ j * t⁻¹ = (t * s) ^ (-j) := by
    rw [← conj_zpow, h1, inv_zpow']
  rw [← h2, inv_mul_cancel_right]

theorem mem_closure_iff (hs : s * s = 1) (ht : t * t = 1) (w : H) :
    w ∈ Subgroup.closure {s, t} ↔ ∃ j : ℤ, w = (t * s) ^ j ∨ w = (t * s) ^ j * s := by
  have hts : t * s ∈ Subgroup.closure {s, t} :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  constructor
  · intro hw
    let E : Subgroup H :=
      { carrier := {w | ∃ j : ℤ, w = (t * s) ^ j ∨ w = (t * s) ^ j * s}
        one_mem' := ⟨0, Or.inl (by simp)⟩
        mul_mem' := by
          rintro a b ⟨i, rfl | rfl⟩ ⟨j, rfl | rfl⟩
          · exact ⟨i + j, Or.inl (zpow_add _ _ _).symm⟩
          · exact ⟨i + j, Or.inr (by rw [zpow_add, mul_assoc])⟩
          · refine ⟨i - j, Or.inr ?_⟩
            rw [mul_assoc, s_mul_zpow hs ht, ← mul_assoc, ← zpow_add, sub_eq_add_neg]
          · refine ⟨i - j, Or.inl ?_⟩
            rw [mul_assoc, ← mul_assoc s, s_mul_zpow hs ht, mul_assoc, hs, mul_one, ← zpow_add,
              sub_eq_add_neg]
        inv_mem' := by
          rintro a ⟨j, rfl | rfl⟩
          · exact ⟨-j, Or.inl (zpow_neg _ _).symm⟩
          · refine ⟨j, Or.inr ?_⟩
            rw [mul_inv_rev, inv_eq_self_of_mul_self hs, ← zpow_neg, s_mul_zpow hs ht, neg_neg] }
    have hle : Subgroup.closure {s, t} ≤ E := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact ⟨0, Or.inr (by simp)⟩
      · refine ⟨1, Or.inr ?_⟩
        rw [zpow_one, mul_assoc, hs, mul_one]
    exact hle hw
  · rintro ⟨j, rfl | rfl⟩
    · exact Subgroup.zpow_mem _ hts j
    · exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hts j) (Subgroup.subset_closure (by simp))

end Dihedral

end CFSG.Quasithin
