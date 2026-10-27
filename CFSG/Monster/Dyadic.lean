module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

namespace CFSG.Monster

open Matrix

@[expose] def dyadic : Subring ℚ where
  carrier := {q | ∃ k : ℕ, q.den ∣ 2 ^ k}
  mul_mem' := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    exact ⟨k + l, (Rat.mul_den_dvd a b).trans (pow_add 2 k l ▸ mul_dvd_mul hk hl)⟩
  one_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    exact ⟨k + l, (Rat.add_den_dvd a b).trans (pow_add 2 k l ▸ mul_dvd_mul hk hl)⟩
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by
    rintro a ⟨k, hk⟩
    exact ⟨k, by rwa [Rat.neg_den]⟩

theorem mem_dyadic {q : ℚ} : q ∈ dyadic ↔ ∃ k : ℕ, q.den ∣ 2 ^ k := Iff.rfl

theorem mem_dyadic_of_sq_mem {q : ℚ} (h : q * q ∈ dyadic) : q ∈ dyadic := by
  obtain ⟨k, hk⟩ := h
  have hden : (q * q).den = q.den * q.den := by rw [← sq, ← sq, Rat.den_pow]
  rw [hden] at hk
  exact ⟨k, (Dvd.intro q.den rfl).trans hk⟩

theorem dyadic_entries_of_conj_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Set (Matrix ι ι ℚ)) (hH : ∀ g ∈ H, ∀ i j, g i j ∈ dyadic)
    (hspan : ∀ M : Matrix ι ι ℚ, (∀ i j, M i j ∈ dyadic) → M ∈ Submodule.span dyadic H)
    (s : Matrix ι ι ℚ) (hs : sᵀ * s = 1) (hconj : ∀ g ∈ H, sᵀ * g * s ∈ H) :
    ∀ i j, s i j ∈ dyadic ∧ s⁻¹ i j ∈ dyadic := by
  rw [Matrix.inv_eq_left_inv hs]
  have hspan_le : ∀ M ∈ Submodule.span dyadic H, ∀ i j, M i j ∈ dyadic := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem x hx => exact hH x hx
    | zero => intro i j; simp
    | add x y _ _ hx hy => intro i j; simpa using dyadic.add_mem (hx i j) (hy i j)
    | smul c x _ hx =>
      intro i j
      have : (c • x) i j = (c : ℚ) * x i j := rfl
      rw [this]
      exact dyadic.mul_mem c.2 (hx i j)
  have hconj_span : ∀ M ∈ Submodule.span dyadic H, sᵀ * M * s ∈ Submodule.span dyadic H := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hconj x hx)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [Matrix.mul_add, Matrix.add_mul]
      exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      have : sᵀ * (c • x) * s = c • (sᵀ * x * s) := by
        change sᵀ * ((c : ℚ) • x) * s = (c : ℚ) • (sᵀ * x * s)
        rw [Matrix.mul_smul, Matrix.smul_mul]
      rw [this]
      exact Submodule.smul_mem _ c hx
  have hentry : ∀ i j, s i j ∈ dyadic := by
    intro i j
    let E : Matrix ι ι ℚ := Matrix.single i i 1
    have hE : E ∈ Submodule.span dyadic H := by
      refine hspan E fun a b => ?_
      by_cases hab : a = i ∧ b = i
      · obtain ⟨rfl, rfl⟩ := hab
        simp [E]
      · have : E a b = 0 := by
          simp only [E, Matrix.single_apply]
          split_ifs with h
          · exact absurd ⟨h.1.symm, h.2.symm⟩ hab
          · rfl
        rw [this]
        exact dyadic.zero_mem
    have hd := hspan_le _ (hconj_span E hE) j j
    have hjj : (sᵀ * E * s) j j = s i j * s i j := by
      simp [E, Matrix.mul_apply, Matrix.single_apply, Matrix.transpose_apply, ite_and,
        Finset.sum_ite_eq, ite_mul]
    rw [hjj] at hd
    exact mem_dyadic_of_sq_mem hd
  exact fun i j => ⟨hentry i j, hentry j i⟩

end CFSG.Monster
