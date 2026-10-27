module

public import CFSG.Quasithin.Vol2.Ch10SecALift

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Quasithin
open scoped Matrix

variable {F : Type} [Field F]

theorem frobPow_apply (a : ℕ) (X : Matrix (Fin 2) (Fin 2) F) (i j : Fin 2) :
    frobPow a X i j = X i j ^ 2 ^ a := rfl

theorem frobPow_mul [CharP F 2] (a : ℕ) (X Y : Matrix (Fin 2) (Fin 2) F) :
    frobPow a (X * Y) = frobPow a X * frobPow a Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ext i j
  simp only [frobPow_apply, Matrix.mul_apply, Fin.sum_univ_two]
  rw [add_pow_char_pow, mul_pow, mul_pow]

theorem frobPow_transpose (a : ℕ) (X : Matrix (Fin 2) (Fin 2) F) :
    frobPow a Xᵀ = (frobPow a X)ᵀ := rfl

theorem frobPow_frobPow {a : ℕ} (hσ : ∀ x : F, (x ^ 2 ^ a) ^ 2 ^ a = x)
    (X : Matrix (Fin 2) (Fin 2) F) : frobPow a (frobPow a X) = X := by
  ext i j
  exact hσ (X i j)

theorem herm_conj [CharP F 2] {a : ℕ} (hσ : ∀ x : F, (x ^ 2 ^ a) ^ 2 ^ a = x)
    {X : Matrix (Fin 2) (Fin 2) F} (hX : (frobPow a X)ᵀ = X) (g : Matrix (Fin 2) (Fin 2) F) :
    (frobPow a (g * X * (frobPow a g)ᵀ))ᵀ = g * X * (frobPow a g)ᵀ := by
  rw [frobPow_mul, frobPow_mul, frobPow_transpose, frobPow_frobPow hσ, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_transpose, hX, Matrix.mul_assoc]

theorem exists_add_frobPow_ne_zero [Finite F] [CharP F 2] {a : ℕ} (ha : 1 ≤ a)
    (hF : Nat.card F = 2 ^ (2 * a)) : ∃ b : F, b + b ^ 2 ^ a ≠ 0 := by
  classical
  have := Fintype.ofFinite F
  by_contra h
  push Not at h
  have hroot : ∀ b : F, b ^ 2 ^ a = b := fun b => by
    have h1 := h b
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h1
    exact h1.symm
  have h1 : 1 < 2 ^ a := Nat.one_lt_two_pow (by omega)
  have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq F h1
  have hne : (Polynomial.X ^ 2 ^ a - Polynomial.X : Polynomial F) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hdeg
    omega
  have hsub : (Finset.univ : Finset F).val ⊆
      (Polynomial.X ^ 2 ^ a - Polynomial.X : Polynomial F).roots := by
    intro x _
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, hroot, sub_self]
  have hcard := Polynomial.card_le_degree_of_subset_roots hsub
  rw [hdeg, Finset.card_univ, ← Nat.card_eq_fintype_card, hF] at hcard
  have : 2 ^ a < 2 ^ (2 * a) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem unipSL_entries (b : F) :
    (unipSL b : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 ∧ (unipSL b : Matrix (Fin 2) (Fin 2) F) 0 1 = b ∧
      (unipSL b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
        (unipSL b : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
  simp [coe_unipSL]

theorem fixed_of_unip [CharP F 2] {a : ℕ} (hσ : ∀ x : F, (x ^ 2 ^ a) ^ 2 ^ a = x)
    (hb0 : ∃ b : F, b + b ^ 2 ^ a ≠ 0) {Y : Matrix (Fin 2) (Fin 2) F}
    (hY : (frobPow a Y)ᵀ = Y)
    (hfix : ∀ b : F, (unipSL b : Matrix (Fin 2) (Fin 2) F) * Y *
      (frobPow a (unipSL b : Matrix (Fin 2) (Fin 2) F))ᵀ = Y) :
    Y 0 1 = 0 ∧ Y 1 0 = 0 ∧ Y 1 1 = 0 := by
  have hsym : Y 1 0 = Y 0 1 ^ 2 ^ a := by
    have := congrFun (congrFun hY 1) 0
    simpa [Matrix.transpose_apply, frobPow_apply] using this.symm
  have hentry : ∀ b : F, ∀ i j : Fin 2, ((unipSL b : Matrix (Fin 2) (Fin 2) F) * Y *
      (frobPow a (unipSL b : Matrix (Fin 2) (Fin 2) F))ᵀ) i j =
      ∑ k : Fin 2, (∑ l : Fin 2, (unipSL b : Matrix (Fin 2) (Fin 2) F) i l * Y l k) *
        (unipSL b : Matrix (Fin 2) (Fin 2) F) j k ^ 2 ^ a := by
    intro b i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, frobPow_apply]
  have h11 : Y 1 1 = 0 := by
    have h1 := congrFun (congrFun (hfix 1) 0) 1
    rw [hentry] at h1
    obtain ⟨e00, e01, e10, e11⟩ := unipSL_entries (1 : F)
    simp only [Fin.sum_univ_two, e00, e01, e10, e11, one_pow, zero_pow (by positivity : 2 ^ a ≠ 0),
      one_mul, mul_one, mul_zero, zero_add] at h1
    linear_combination h1
  have h00 : ∀ b : F, b * Y 1 0 + Y 0 1 * b ^ 2 ^ a = 0 := by
    intro b
    have h1 := congrFun (congrFun (hfix b) 0) 0
    rw [hentry] at h1
    obtain ⟨e00, e01, -, -⟩ := unipSL_entries b
    simp only [Fin.sum_univ_two, e00, e01, one_pow, one_mul, mul_one, mul_zero, add_zero,
      h11] at h1
    linear_combination h1
  have h01 : Y 0 1 = 0 := by
    by_contra hc
    obtain ⟨b0, hb0⟩ := hb0
    have hσc : Y 0 1 ^ 2 ^ a ≠ 0 := pow_ne_zero _ hc
    have h2 := h00 (b0 * (Y 0 1 ^ 2 ^ a)⁻¹)
    rw [hsym, mul_pow, inv_pow, hσ] at h2
    have e : Y 0 1 * (b0 ^ 2 ^ a * (Y 0 1)⁻¹) = b0 ^ 2 ^ a := by field_simp
    rw [inv_mul_cancel_right₀ hσc, e] at h2
    exact hb0 h2
  exact ⟨h01, by rw [hsym, h01, zero_pow (by positivity)], h11⟩

theorem twist_apply_zero_zero {a : ℕ} (ψ Y : Matrix (Fin 2) (Fin 2) F) (h01 : Y 0 1 = 0)
    (h10 : Y 1 0 = 0) (h11 : Y 1 1 = 0) :
    (ψ * Y * (frobPow a ψ)ᵀ) 0 0 = ψ 0 0 * Y 0 0 * ψ 0 0 ^ 2 ^ a := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, frobPow_apply, Matrix.transpose_apply, h01, h10,
    h11]

end CFSG.Quasithin.Vol2.Ch10.SecA
