module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiEigen
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo

open Matrix

private theorem fin_three_pairwise_ne_of_add_eq_zero :
    ∀ a b c : Fin 3, a + b + c = 0 → ¬ (a = b ∧ b = c) → a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  decide

section Split

variable {L : Type} [Field L] [CharP L 2]

private theorem eq_one_of_mul_self_eq_one_of_charTwo {d : L} (hd : d * d = 1) : d = 1 := by
  have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
  have h : (d + 1) * (d + 1) = 0 := by linear_combination hd + (d + 1) * h2
  have h' : d + 1 = 0 := mul_self_eq_zero.mp h
  linear_combination h' - h2

private theorem entry_eq_zero_of_commute_diag {d : Fin 3 → L}
    {M : Matrix (Fin 3) (Fin 3) L} (h : M * diagonal d = diagonal d * M) {i j : Fin 3}
    (hij : d i ≠ d j) : M i j = 0 := by
  have e := congrFun (congrFun h i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at e
  have h0 : M i j * (d j - d i) = 0 := by rw [mul_sub, e, mul_comm, sub_self]
  exact (mul_eq_zero.mp h0).resolve_right (sub_ne_zero.mpr (Ne.symm hij))

private theorem eq_one_of_commute_diag_of_mul_self {d : Fin 3 → L} (h01 : d 0 ≠ d 1)
    (h02 : d 0 ≠ d 2) (h12 : d 1 ≠ d 2) {M : Matrix (Fin 3) (Fin 3) L}
    (hMD : M * diagonal d = diagonal d * M) (hMM : M * M = 1) : M = 1 := by
  have m01 := entry_eq_zero_of_commute_diag hMD (i := 0) (j := 1) h01
  have m02 := entry_eq_zero_of_commute_diag hMD (i := 0) (j := 2) h02
  have m12 := entry_eq_zero_of_commute_diag hMD (i := 1) (j := 2) h12
  have m10 := entry_eq_zero_of_commute_diag hMD (i := 1) (j := 0) (Ne.symm h01)
  have m20 := entry_eq_zero_of_commute_diag hMD (i := 2) (j := 0) (Ne.symm h02)
  have m21 := entry_eq_zero_of_commute_diag hMD (i := 2) (j := 1) (Ne.symm h12)
  have e0 := congrFun (congrFun hMM 0) 0
  have e1 := congrFun (congrFun hMM 1) 1
  have e2 := congrFun (congrFun hMM 2) 2
  simp only [Matrix.mul_apply, Fin.sum_univ_three, m01, m02, m12, m10, m20, m21, mul_zero,
    zero_mul, add_zero, zero_add, Matrix.one_apply_eq] at e0 e1 e2
  have d0 := eq_one_of_mul_self_eq_one_of_charTwo e0
  have d1 := eq_one_of_mul_self_eq_one_of_charTwo e1
  have d2 := eq_one_of_mul_self_eq_one_of_charTwo e2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [m01, m02, m12, m10, m20, m21, d0, d1, d2]

theorem eq_one_of_commute_of_tau {τ : L} (hτ : τ ^ 2 + τ + 1 = 0)
    {A B : Matrix (Fin 3) (Fin 3) L} (hA3 : A ^ 3 = 1) (hdet : A.det = 1)
    (hAs : ∀ c : L, A ≠ c • (1 : Matrix (Fin 3) (Fin 3) L)) (hAB : A * B = B * A)
    (hB : B * B = 1) : B = 1 := by
  have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
  have hτ3 : τ ^ 3 = 1 := by linear_combination (τ - 1) * hτ
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    exact one_ne_zero (by linear_combination hτ - h2 : (1 : L) = 0)
  have h3 : (3 : L) ≠ 0 := fun h => one_ne_zero (by linear_combination h - h2 : (1 : L) = 0)
  have hinj : ∀ a b : Fin 3, τ ^ (a : ℕ) = τ ^ (b : ℕ) → a = b := by
    intro a b hab
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hfin : IsOfFinOrder τ := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hτ3⟩
    rw [hfin.pow_inj_mod, orderOf_eq_prime hτ3 hτ1, Nat.mod_eq_of_lt a.2,
      Nat.mod_eq_of_lt b.2] at hab
    exact Fin.ext hab
  obtain ⟨b, hb, hk⟩ := Sec4.exists_eigenbasis hτ3 hτ1 h3 hA3
  choose k hk using hk
  have hPu : IsUnit (Sec4.colMat b) := Sec4.isUnit_colMat hb
  have hPdet : IsUnit (Sec4.colMat b).det := (Matrix.isUnit_iff_isUnit_det _).mp hPu
  set P := Sec4.colMat b with hP
  set d : Fin 3 → L := fun i => τ ^ (k i : ℕ) with hd
  have hAP : A * P = P * diagonal d := Sec4.mul_colMat_eq (c := d) hk
  have hPinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPdet
  have hPinv' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPdet
  have hprod : d 0 * d 1 * d 2 = 1 := by
    have e := congrArg Matrix.det hAP
    rw [Matrix.det_mul, Matrix.det_mul, hdet, one_mul, Matrix.det_diagonal,
      Fin.prod_univ_three] at e
    exact mul_left_cancel₀ hPdet.ne_zero (e.symm.trans (mul_one _).symm)
  have hsum : k 0 + k 1 + k 2 = 0 := by
    apply hinj
    rw [Sec4.tau_pow_fin_add hτ3, Sec4.tau_pow_fin_add hτ3]
    simpa [hd] using hprod
  have hnc : ¬ (k 0 = k 1 ∧ k 1 = k 2) := by
    rintro ⟨h01, h12⟩
    apply hAs (τ ^ (k 0 : ℕ))
    have hdc : diagonal d = τ ^ (k 0 : ℕ) • (1 : Matrix (Fin 3) (Fin 3) L) := by
      rw [Matrix.smul_one_eq_diagonal]
      congr 1
      funext i
      fin_cases i <;> simp [hd, h01, h12]
    have e : A * P = (τ ^ (k 0 : ℕ) • (1 : Matrix (Fin 3) (Fin 3) L)) * P := by
      rw [hAP, hdc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]
    exact hPu.mul_left_inj.mp e
  obtain ⟨k01, k02, k12⟩ := fin_three_pairwise_ne_of_add_eq_zero _ _ _ hsum hnc
  have hD : diagonal d = P⁻¹ * A * P := by
    rw [Matrix.mul_assoc, hAP, ← Matrix.mul_assoc, hPinv, Matrix.one_mul]
  have hMD : P⁻¹ * B * P * diagonal d = diagonal d * (P⁻¹ * B * P) := by
    rw [hD]
    calc P⁻¹ * B * P * (P⁻¹ * A * P) = P⁻¹ * (B * (P * P⁻¹) * A) * P := by
          simp only [Matrix.mul_assoc]
      _ = P⁻¹ * (A * (P * P⁻¹) * B) * P := by rw [hPinv', Matrix.mul_one, Matrix.mul_one, hAB]
      _ = P⁻¹ * A * P * (P⁻¹ * B * P) := by simp only [Matrix.mul_assoc]
  have hMM : P⁻¹ * B * P * (P⁻¹ * B * P) = 1 := by
    calc P⁻¹ * B * P * (P⁻¹ * B * P) = P⁻¹ * (B * (P * P⁻¹) * B) * P := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPinv', Matrix.mul_one, hB, Matrix.mul_one, hPinv]
  have hM1 := eq_one_of_commute_diag_of_mul_self (fun h => k01 (hinj _ _ h))
    (fun h => k02 (hinj _ _ h)) (fun h => k12 (hinj _ _ h)) hMD hMM
  calc B = (P * P⁻¹) * B * (P * P⁻¹) := by rw [hPinv', Matrix.one_mul, Matrix.mul_one]
    _ = P * (P⁻¹ * B * P) * P⁻¹ := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hM1, Matrix.mul_one, hPinv']

end Split

theorem eq_one_of_commute_of_pow_three_eq_one {F : Type} [Field F] [CharP F 2]
    {A B : Matrix (Fin 3) (Fin 3) F} (hA3 : A ^ 3 = 1) (hdet : A.det = 1)
    (hAs : ∀ c : F, A ≠ c • (1 : Matrix (Fin 3) (Fin 3) F)) (hAB : A * B = B * A)
    (hB : B * B = 1) : B = 1 := by
  set φ : F →+* AlgebraicClosure F := algebraMap F (AlgebraicClosure F)
  obtain ⟨τ, hτ⟩ := IsAlgClosed.exists_root
    (Polynomial.C (1 : AlgebraicClosure F) * Polynomial.X ^ 2 + Polynomial.C 1 * Polynomial.X +
      Polynomial.C 1) (by rw [Polynomial.degree_quadratic one_ne_zero]; decide)
  have hτ' : τ ^ 2 + τ + 1 = 0 := by simpa using hτ.eq_zero
  have hinj : Function.Injective (φ.mapMatrix : Matrix (Fin 3) (Fin 3) F → _) :=
    Matrix.map_injective φ.injective
  have hAs' : ∀ c : AlgebraicClosure F, φ.mapMatrix A ≠ c • (1 : Matrix (Fin 3) (Fin 3) _) := by
    intro c hc
    apply hAs (A 0 0)
    apply hinj
    have h00 : φ (A 0 0) = c := by
      have := congrFun (congrFun hc 0) 0
      simpa using this
    rw [hc]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [h00]
    · simp [Matrix.one_apply_ne hij]
  have hB' := eq_one_of_commute_of_tau hτ' (A := φ.mapMatrix A) (B := φ.mapMatrix B)
    (by rw [← map_pow, hA3, map_one]) (by rw [← RingHom.map_det, hdet, map_one]) hAs'
    (by rw [← map_mul, hAB, map_mul]) (by rw [← map_mul, hB, map_one])
  exact hinj (hB'.trans (map_one _).symm)

end CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo

end
