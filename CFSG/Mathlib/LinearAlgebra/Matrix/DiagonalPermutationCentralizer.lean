module

public import Mathlib.LinearAlgebra.Matrix.Permutation

public section

namespace Matrix

theorem eq_scalar_of_commute_diag2n_permMatrix
    {F : Type} [Field F] {n : ℕ} (hn : 3 ≤ n)
    (omega : Fˣ) (hne : omega ≠ 1) (M : Matrix (Fin n) (Fin n) F)
    (hdiagComm : ∀ i k : Fin n, ∀ hik : i ≠ k,
      M * ((SpecialLinearGroup.diag2n hik (omega : F) omega.ne_zero) : Matrix (Fin n) (Fin n) F) =
        ((SpecialLinearGroup.diag2n hik (omega : F) omega.ne_zero) : Matrix (Fin n) (Fin n) F) * M)
    (hpermComm : ∀ i j : Fin n, M * Equiv.Perm.permMatrix F (Equiv.swap i j) = Equiv.Perm.permMatrix F (Equiv.swap i j) * M) :
    M = Matrix.scalar (Fin n) (M ⟨0, by omega⟩ ⟨0, by omega⟩) := by
  classical
  have hdiag : ∀ i j : Fin n, i ≠ j → M i j = 0 := by
    intro i j hij
    obtain ⟨k, hki, hkj⟩ := ENat.exists_ne_ne_of_three_le
      (by simpa only [ENat.card_eq_coe_fintype_card, Fintype.card_fin] using
        (show (3 : ENat) ≤ (n : ENat) from by exact_mod_cast hn)) i j
    have h := congrArg (fun N : Matrix (Fin n) (Fin n) F => N i j) (hdiagComm i k (Ne.symm hki))
    rw [SpecialLinearGroup.diag2n_coe, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    have hji : j ≠ i := Ne.symm hij
    have hjk : j ≠ k := Ne.symm hkj
    simp only [if_neg hji, if_neg hjk, if_true, mul_one] at h
    have he : M i j * ((omega : F) - 1) = 0 := by
      rw [mul_sub, mul_one, mul_comm (M i j) (omega : F), ← h, sub_self]
    have hval : (omega : F) ≠ 1 := fun ho => hne (Units.ext ho)
    exact (mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr hval)
  have heq : ∀ i j : Fin n, M i i = M j j := by
    intro i j
    have h := congrArg (fun N : Matrix (Fin n) (Fin n) F => N i j) (hpermComm i j)
    have hsum : ∀ x : Fin n, ((Equiv.swap i j) x = j) ↔ x = i := by
      intro x
      constructor
      · intro hx
        apply (Equiv.swap i j).injective
        rw [hx, Equiv.swap_apply_left]
      · intro hx
        rw [hx]
        exact Equiv.swap_apply_left i j
    simp only [Matrix.mul_apply, Equiv.Perm.permMatrix] at h
    simpa [hsum, Equiv.swap_apply_left, Equiv.swap_apply_right] using h
  ext i j
  by_cases hij : i = j
  · subst j
    simpa only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] using heq i ⟨0, by omega⟩
  · rw [hdiag i j hij]
    simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]

end Matrix
