module

public import Mathlib.FieldTheory.Finite.Basic
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma18iiiM
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Diag
public import CFSG.LieType.Universal.Unitary.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res424Seven

open Matrix
open scoped MatrixGroups

section SL2

variable {K : Type} [Field K]

theorem exists_normForm_eq_neg_one [Finite K] (h3 : (3 : K) ≠ 0) :
    ∃ α β : K, α ^ 2 - α * β + β ^ 2 = -1 := by
  classical
  have := Fintype.ofFinite K
  by_cases h2 : ringChar K = 2
  · have : CharP K 2 := ringChar.of_eq h2
    refine ⟨1, 0, ?_⟩
    rw [CharTwo.neg_eq]
    ring
  · have hodd : Fintype.card K % 2 = 1 := FiniteField.odd_card_of_char_ne_two h2
    have h20 : (2 : K) ≠ 0 := Ring.two_ne_zero h2
    have hf : (Polynomial.X ^ 2 : Polynomial K).degree = 2 := by
      rw [Polynomial.degree_X_pow]
      rfl
    have hg : (Polynomial.C (3 : K) * Polynomial.X ^ 2 + Polynomial.C 4).degree = 2 := by
      rw [Polynomial.degree_add_C (by rw [Polynomial.degree_C_mul_X_pow 2 h3]; norm_num),
        Polynomial.degree_C_mul_X_pow 2 h3]
      rfl
    obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic hf hg hodd
    simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C] at hab
    refine ⟨(a + b) / 2, b, ?_⟩
    field_simp
    linear_combination hab

theorem trace_eq_neg_one_of_pow_three {A : SL(2, K)} (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1) :
    (A : Matrix (Fin 2) (Fin 2) K).trace = -1 := by
  obtain ⟨a, b, c, e, hM⟩ : ∃ a b c e : K, (A : Matrix (Fin 2) (Fin 2) K) = !![a, b; c, e] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : a * e - b * c = 1 := by
    have h := A.det_coe
    rwa [hM, Matrix.det_fin_two_of] at h
  have h3 : (A : Matrix (Fin 2) (Fin 2) K) * A * A = 1 := by
    have h := congrArg (fun B : SL(2, K) => (B : Matrix (Fin 2) (Fin 2) K)) hA3
    simpa only [pow_succ, pow_zero, one_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_one] using h
  rw [hM] at h3
  have e00 : (a * a + b * c) * a + (a * b + b * e) * c = 1 := by
    have h := congrFun (congrFun h3 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have e01 : (a * a + b * c) * b + (a * b + b * e) * e = 0 := by
    have h := congrFun (congrFun h3 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have e10 : (c * a + e * c) * a + (c * b + e * e) * c = 0 := by
    have h := congrFun (congrFun h3 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have e11 : (c * a + e * c) * b + (c * b + e * e) * e = 1 := by
    have h := congrFun (congrFun h3 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  rw [hM, Matrix.trace_fin_two_of]
  have hb : b * ((a + e) ^ 2 - 1) = 0 := by linear_combination e01 + b * hdet
  have hc : c * ((a + e) ^ 2 - 1) = 0 := by linear_combination e10 + c * hdet
  have ha : a * ((a + e) ^ 2 - 1) - (a + e) = 1 := by
    linear_combination e00 + (2 * a + e) * hdet
  have he : e * ((a + e) ^ 2 - 1) - (a + e) = 1 := by
    linear_combination e11 + (a + 2 * e) * hdet
  by_contra ht
  have hsq : (a + e) ^ 2 - 1 ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_sub] at ha
    exact ht (by linear_combination -ha)
  have hb0 : b = 0 := (mul_eq_zero.mp hb).resolve_right hsq
  have hc0 : c = 0 := (mul_eq_zero.mp hc).resolve_right hsq
  have hae : a = e := by
    have h1 : (a - e) * ((a + e) ^ 2 - 1) = 0 := by linear_combination ha - he
    exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hsq)
  have hcub : (a - 1) * (2 * a + 1) ^ 2 = 0 := by
    rw [← hae] at ha
    linear_combination ha
  rcases mul_eq_zero.mp hcub with h1 | h1
  · apply hA1
    apply Subtype.ext
    rw [hM, ← hae, sub_eq_zero.mp h1, hb0, hc0]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · have h2 : 2 * a + 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp h1
    exact ht (by linear_combination h2 - hae)

theorem companion_conj (α β : K) :
    !![-β, α; α - β, β] * !![(0 : K), -1; 1, -1] =
      !![(-1 : K), 1; -1, 0] * !![-β, α; α - β, β] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem exists_conj_eq_inv_sl2 [Finite K] (h3 : (3 : K) ≠ 0) {A : SL(2, K)} (hA3 : A ^ 3 = 1)
    (hA1 : A ≠ 1) : ∃ N : SL(2, K), N * A * N⁻¹ = A⁻¹ := by
  have htr := trace_eq_neg_one_of_pow_three hA3 hA1
  have h4 : (A : Matrix (Fin 2) (Fin 2) K).trace ^ 2 ≠ 4 := by
    rw [htr]
    intro h
    exact h3 (by linear_combination -h)
  obtain ⟨h, hdet, hAh⟩ :=
    CFSG.GH74.GLS.IVK.Proofs2.Lemma18iii.conj_traces_exists_intertwiner A.det_coe h4
  rw [htr] at hAh
  obtain ⟨α, β, hαβ⟩ := exists_normForm_eq_neg_one h3
  set N' : Matrix (Fin 2) (Fin 2) K := !![-β, α; α - β, β] with hN'
  have hN'det : N'.det = 1 := by
    rw [hN', Matrix.det_fin_two_of]
    linear_combination -hαβ
  have hu : IsUnit h := (Matrix.isUnit_iff_isUnit_det h).2 (isUnit_iff_ne_zero.2 hdet)
  have hud : IsUnit h.det := isUnit_iff_ne_zero.2 hdet
  have hNdet : (h * N' * h⁻¹).det = 1 := by rw [Matrix.det_conj hu, hN'det]
  obtain ⟨N, hNcoe⟩ : ∃ N : SL(2, K), (N : Matrix (Fin 2) (Fin 2) K) = h * N' * h⁻¹ :=
    ⟨⟨h * N' * h⁻¹, hNdet⟩, rfl⟩
  refine ⟨N, ?_⟩
  set M := (A : Matrix (Fin 2) (Fin 2) K) with hMdef
  set C : Matrix (Fin 2) (Fin 2) K := !![0, -1; 1, -1] with hC
  set C' : Matrix (Fin 2) (Fin 2) K := !![-1, 1; -1, 0] with hC'
  have hCC' : C * C' = 1 := by
    rw [hC, hC']
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h1 : h⁻¹ * M = C * h⁻¹ := by
    calc h⁻¹ * M = h⁻¹ * M * (h * h⁻¹) := by rw [Matrix.mul_nonsing_inv h hud, mul_one]
      _ = h⁻¹ * (M * h) * h⁻¹ := by simp only [Matrix.mul_assoc]
      _ = h⁻¹ * (h * C) * h⁻¹ := by rw [hAh]
      _ = C * h⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul h hud, Matrix.one_mul]
  have hadj : M.adjugate * M = 1 := by
    rw [Matrix.adjugate_mul, A.det_coe, one_smul]
  have h2 : M.adjugate * h = h * C' := by
    calc M.adjugate * h = M.adjugate * h * (C * C') := by rw [hCC', mul_one]
      _ = M.adjugate * (h * C) * C' := by simp only [Matrix.mul_assoc]
      _ = M.adjugate * (M * h) * C' := by rw [hAh]
      _ = h * C' := by rw [← Matrix.mul_assoc, hadj, Matrix.one_mul]
  have key : N * A = A⁻¹ * N := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, hNcoe]
    change h * N' * h⁻¹ * M = M.adjugate * (h * N' * h⁻¹)
    calc h * N' * h⁻¹ * M = h * N' * (h⁻¹ * M) := by simp only [Matrix.mul_assoc]
      _ = h * (N' * C) * h⁻¹ := by rw [h1]; simp only [Matrix.mul_assoc]
      _ = h * (C' * N') * h⁻¹ := by rw [hN', hC, hC', companion_conj]
      _ = M.adjugate * h * N' * h⁻¹ := by rw [h2]; simp only [Matrix.mul_assoc]
      _ = M.adjugate * (h * N' * h⁻¹) := by simp only [Matrix.mul_assoc]
  rw [key, mul_inv_cancel_right]

end SL2

section Cyc

variable {R : Type*} [CommRing R]

@[expose] def cyc3 (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem cyc3_mul_diagonal (ν : Fin 3 → R) :
    cyc3 R * diagonal ν = diagonal ![ν 2, ν 0, ν 1] * cyc3 R := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cyc3, Matrix.mul_apply, Matrix.diagonal_apply]

theorem det_cyc3 : (cyc3 R).det = 1 := by
  simp [cyc3, Matrix.det_fin_three]

theorem cyc3_transpose_mul : (cyc3 R)ᵀ * cyc3 R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyc3, Matrix.mul_apply, Fin.sum_univ_three]

end Cyc

section Rot

variable {K : Type} [Field K]

theorem rot_eq_smul {ν : Fin 3 → K} (hν : ∀ i, ν i ^ 3 = 1) (hprod : ν 0 * ν 1 * ν 2 = 1) :
    (![ν 2, ν 0, ν 1] : Fin 3 → K) = (ν 0 * (ν 1)⁻¹) • ν := by
  have h1 : ν 1 ≠ 0 := fun h => by simpa [h] using hν 1
  have e0 : ν 1 * ν 2 = ν 0 * ν 0 := by linear_combination ν 0 ^ 2 * hprod - ν 1 * ν 2 * hν 0
  have e2 : ν 0 * ν 2 = ν 1 * ν 1 := by linear_combination ν 1 ^ 2 * hprod - ν 0 * ν 2 * hν 1
  funext i
  fin_cases i
  · show ν 2 = ν 0 * (ν 1)⁻¹ * ν 0
    calc ν 2 = ν 1 * ν 2 * (ν 1)⁻¹ := by rw [mul_comm (ν 1), mul_inv_cancel_right₀ h1]
      _ = ν 0 * (ν 1)⁻¹ * ν 0 := by rw [e0]; ring
  · show ν 0 = ν 0 * (ν 1)⁻¹ * ν 1
    rw [inv_mul_cancel_right₀ h1]
  · show ν 1 = ν 0 * (ν 1)⁻¹ * ν 2
    calc ν 1 = ν 1 * ν 1 * (ν 1)⁻¹ := by rw [mul_inv_cancel_right₀ h1]
      _ = ν 0 * (ν 1)⁻¹ * ν 2 := by rw [← e2]; ring

theorem conj_cyc3_mul {X P Q : Matrix (Fin 3) (Fin 3) K} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    {ν : Fin 3 → K} (hXP : X * P = P * diagonal ν) (hν : ∀ i, ν i ^ 3 = 1)
    (hprod : ν 0 * ν 1 * ν 2 = 1) :
    (P * cyc3 K * Q) * X = (ν 0 * (ν 1)⁻¹) • (X * (P * cyc3 K * Q)) := by
  have hX : X = P * diagonal ν * Q := by
    calc X = X * (P * Q) := by rw [hPQ, mul_one]
      _ = P * diagonal ν * Q := by rw [← Matrix.mul_assoc, hXP]
  have hrot : cyc3 K * diagonal ν = (ν 0 * (ν 1)⁻¹) • (diagonal ν * cyc3 K) := by
    rw [cyc3_mul_diagonal, rot_eq_smul hν hprod, ← Matrix.smul_mul, Matrix.diagonal_smul]
  rw [hX]
  calc P * cyc3 K * Q * (P * diagonal ν * Q) = P * (cyc3 K * (Q * P) * diagonal ν) * Q := by
        simp only [Matrix.mul_assoc]
    _ = P * ((ν 0 * (ν 1)⁻¹) • (diagonal ν * cyc3 K)) * Q := by
        rw [hQP, Matrix.mul_one, hrot]
    _ = (ν 0 * (ν 1)⁻¹) • (P * diagonal ν * (Q * P) * cyc3 K * Q) := by
        rw [hQP, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul]
        simp only [Matrix.mul_assoc]
    _ = (ν 0 * (ν 1)⁻¹) • (P * diagonal ν * Q * (P * cyc3 K * Q)) := by
        simp only [Matrix.mul_assoc]

theorem exists_eigen_of_diag {X P Q : Matrix (Fin 3) (Fin 3) K} (hPQ : P * Q = 1)
    (hQP : Q * P = 1) (hdiag : ∀ i j, i ≠ j → (Q * X * P) i j = 0) (hX3 : X ^ 3 = 1)
    (hdet : X.det = 1) (hX : ∀ μ : K, X ≠ Matrix.scalar (Fin 3) μ) :
    ∃ ν : Fin 3 → K, X * P = P * diagonal ν ∧ (∀ i, ν i ^ 3 = 1) ∧ ν 0 * ν 1 * ν 2 = 1 ∧
      ν 0 ≠ ν 1 ∧ ν 1 ≠ ν 2 ∧ ν 0 ≠ ν 2 := by
  set ν : Fin 3 → K := fun i => (Q * X * P) i i with hν
  have hD : Q * X * P = diagonal ν := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij, hdiag i j hij]
  have hXP : X * P = P * diagonal ν := by
    rw [← hD, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hX' : X = P * diagonal ν * Q := by
    calc X = X * (P * Q) := by rw [hPQ, Matrix.mul_one]
      _ = P * diagonal ν * Q := by rw [← Matrix.mul_assoc, hXP]
  have hcube : diagonal ν ^ 3 = 1 := by
    have h : (Q * X * P) ^ 3 = Q * X ^ 3 * P := by
      rw [pow_three, pow_three]
      calc Q * X * P * (Q * X * P * (Q * X * P)) = Q * X * (P * Q) * X * (P * Q) * X * P := by
            simp only [Matrix.mul_assoc]
        _ = Q * (X * (X * X)) * P := by rw [hPQ]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    rw [← hD, h, hX3, Matrix.mul_one, hQP]
  have hν3 : ∀ i, ν i ^ 3 = 1 := by
    intro i
    have h := congrFun (congrFun hcube i) i
    simpa [Matrix.diagonal_pow] using h
  have hprod : ν 0 * ν 1 * ν 2 = 1 := by
    have h : (Q * X * P).det = 1 := by
      rw [Matrix.det_mul, Matrix.det_mul, hdet, mul_one, ← Matrix.det_mul, hQP, Matrix.det_one]
    rwa [hD, Matrix.det_diagonal, Fin.prod_univ_three] at h
  have hscal : ∀ μ : K, ν 0 = μ → ν 1 = μ → ν 2 = μ → False := by
    intro μ h0 h1 h2
    apply hX μ
    have hdμ : diagonal ν = Matrix.scalar (Fin 3) μ := by
      ext i j
      rw [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
      fin_cases i <;> fin_cases j <;> simp [h0, h1, h2]
    rw [hX', hdμ, Matrix.scalar_apply, Matrix.mul_assoc, ← Matrix.smul_eq_diagonal_mul,
      Matrix.mul_smul, hPQ, Matrix.smul_one_eq_diagonal]
  refine ⟨ν, hXP, hν3, hprod, fun h01 => ?_, fun h12 => ?_, fun h02 => ?_⟩
  · refine hscal (ν 0) rfl h01.symm ?_
    rw [← h01] at hprod
    linear_combination ν 0 * hprod - ν 2 * hν3 0
  · refine hscal (ν 1) ?_ rfl h12.symm
    rw [← h12] at hprod
    linear_combination ν 1 * hprod - ν 0 * hν3 1
  · refine hscal (ν 0) rfl ?_ h02.symm
    rw [← h02] at hprod
    linear_combination ν 0 * hprod - ν 1 * hν3 0

theorem lambda_spec {ν : Fin 3 → K} (hν : ∀ i, ν i ^ 3 = 1) (h01 : ν 0 ≠ ν 1) :
    (ν 0 * (ν 1)⁻¹) ^ 3 = 1 ∧ ν 0 * (ν 1)⁻¹ ≠ 1 := by
  have h1 : ν 1 ≠ 0 := fun h => by simpa [h] using hν 1
  refine ⟨by rw [mul_pow, inv_pow, hν 0, hν 1, inv_one, mul_one], fun h => h01 ?_⟩
  calc ν 0 = ν 0 * (ν 1)⁻¹ * ν 1 := by rw [inv_mul_cancel_right₀ h1]
    _ = ν 1 := by rw [h, one_mul]

open CFSG.GH74.GLS.Stage2.Bender.Thm1 in
theorem exists_rot_sl3 [Finite K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1)
    {X : Matrix.SpecialLinearGroup (Fin 3) K} (hX3 : X ^ 3 = 1)
    (hX : ∀ μ : K, (X : Matrix (Fin 3) (Fin 3) K) ≠ Matrix.scalar (Fin 3) μ) :
    ∃ (G : Matrix.SpecialLinearGroup (Fin 3) K) (l : K), l ^ 3 = 1 ∧ l ≠ 1 ∧
      ((G * X : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        l • ((X * G : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  obtain ⟨y, hy⟩ := exists_diagonalizing_of_commuting_cube_one ω hω hω1 (Subgroup.zpowers X)
    (fun x hx => by
      obtain ⟨k, rfl⟩ := hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm k, zpow_mul, zpow_natCast, hX3, one_zpow])
    (fun x hx x' hx' => by
      obtain ⟨k, rfl⟩ := hx
      obtain ⟨k', rfl⟩ := hx'
      exact (Commute.zpow_zpow_self X k k').eq)
  set P : Matrix (Fin 3) (Fin 3) K := ((y⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) with hP
  set Q : Matrix (Fin 3) (Fin 3) K := (y : Matrix (Fin 3) (Fin 3) K) with hQ
  have hPQ : P * Q = 1 := by
    rw [hP, hQ, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hQP : Q * P = 1 := by
    rw [hP, hQ, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hdiag : ∀ i j, i ≠ j → (Q * (X : Matrix (Fin 3) (Fin 3) K) * P) i j = 0 := by
    intro i j hij
    have h := hy X (Subgroup.mem_zpowers X) i j hij
    rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h
  have hX3' : (X : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hX3, Matrix.SpecialLinearGroup.coe_one]
  obtain ⟨ν, hXP, hν3, hprod, h01, -, -⟩ :=
    exists_eigen_of_diag hPQ hQP hdiag hX3' X.det_coe hX
  obtain ⟨hl3, hl1⟩ := lambda_spec hν3 h01
  set Pc : Matrix.SpecialLinearGroup (Fin 3) K := ⟨cyc3 K, det_cyc3⟩ with hPc
  refine ⟨y⁻¹ * Pc * y, ν 0 * (ν 1)⁻¹, hl3, hl1, ?_⟩
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  exact conj_cyc3_mul hPQ hQP hXP hν3 hprod

open CFSG.LieType.Universal.Unitary in
theorem conjTr_conjTr {σ : K ≃+* K} (hσσ : ∀ x, σ (σ x) = x) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) : conjTr σ (conjTr σ A) = A := by
  ext i j
  simp [conjTr, hσσ]

open CFSG.LieType.Universal.Unitary in
theorem conjTr_diagonal (σ : K ≃+* K) {n : ℕ} (ν : Fin n → K) :
    conjTr σ (diagonal ν) = diagonal (fun i => σ (ν i)) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [conjTr]
  · simp [conjTr, Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij)]

open CFSG.LieType.Universal.Unitary in
theorem det_conjTr (σ : K ≃+* K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    (conjTr σ A).det = σ A.det := by
  rw [conjTr, Matrix.det_transpose, RingEquiv.map_det σ A]
  rfl

open CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.LieType.Universal.Unitary in
theorem exists_rot_unitary [Finite K] (σ : K ≃+* K) (hσσ : ∀ x, σ (σ x) = x)
    (hnorm : ∀ c : K, c ≠ 0 → σ c = c → ∃ a, σ a * a = c)
    (hσ3 : ∀ x : K, x ^ 3 = 1 → σ x * x = 1) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1)
    {X : Matrix (Fin 3) (Fin 3) K} (hdet : X.det = 1) (hU : conjTr σ X * X = 1)
    (hX3 : X ^ 3 = 1) (hX : ∀ μ : K, X ≠ Matrix.scalar (Fin 3) μ) :
    ∃ G : Matrix (Fin 3) (Fin 3) K, G.det = 1 ∧ conjTr σ G * G = 1 ∧
      ∃ l : K, l ^ 3 = 1 ∧ l ≠ 1 ∧ G * X = l • (X * G) := by
  set Xs : Matrix.SpecialLinearGroup (Fin 3) K := ⟨X, hdet⟩ with hXs
  have hXs3 : Xs ^ 3 = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    exact hX3)
  obtain ⟨y, hy⟩ := exists_diagonalizing_of_commuting_cube_one ω hω hω1 (Subgroup.zpowers Xs)
    (fun x hx => by
      obtain ⟨k, rfl⟩ := hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm k, zpow_mul, zpow_natCast, hXs3, one_zpow])
    (fun x hx x' hx' => by
      obtain ⟨k, rfl⟩ := hx
      obtain ⟨k', rfl⟩ := hx'
      exact (Commute.zpow_zpow_self Xs k k').eq)
  set P : Matrix (Fin 3) (Fin 3) K := ((y⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) with hP
  set Q : Matrix (Fin 3) (Fin 3) K := (y : Matrix (Fin 3) (Fin 3) K) with hQ
  have hPQ : P * Q = 1 := by
    rw [hP, hQ, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hQP : Q * P = 1 := by
    rw [hP, hQ, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hdiag : ∀ i j, i ≠ j → (Q * X * P) i j = 0 := by
    intro i j hij
    have h := hy Xs (Subgroup.mem_zpowers Xs) i j hij
    rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h
  obtain ⟨ν, hXP, hν3, hprod, h01, h12, h02⟩ := exists_eigen_of_diag hPQ hQP hdiag hX3 hdet hX
  have hDD : diagonal ν * diagonal (fun i => σ (ν i)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [mul_comm]
    exact hσ3 _ (hν3 i)
  have hstar : diagonal ν * conjTr σ P = conjTr σ P * X := by
    have h1 : conjTr σ P * conjTr σ X = diagonal (fun i => σ (ν i)) * conjTr σ P := by
      rw [← conjTr_mul, hXP, conjTr_mul, conjTr_diagonal]
    calc diagonal ν * conjTr σ P = diagonal ν * (conjTr σ P * (conjTr σ X * X)) := by
          rw [hU, Matrix.mul_one]
      _ = diagonal ν * (diagonal (fun i => σ (ν i)) * conjTr σ P) * X := by
          rw [← Matrix.mul_assoc (conjTr σ P), h1]; simp only [Matrix.mul_assoc]
      _ = conjTr σ P * X := by
          rw [← Matrix.mul_assoc, hDD, Matrix.one_mul]
  obtain ⟨Γ, hΓ⟩ : ∃ Γ, Γ = conjTr σ P * P := ⟨_, rfl⟩
  have hΓD : diagonal ν * Γ = Γ * diagonal ν := by
    rw [hΓ, ← Matrix.mul_assoc, hstar, Matrix.mul_assoc, hXP, Matrix.mul_assoc]
  have hνinj : ∀ i j, i ≠ j → ν i ≠ ν j := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first | exact absurd rfl hij | skip
    · exact h01
    · exact h02
    · exact Ne.symm h01
    · exact h12
    · exact Ne.symm h02
    · exact Ne.symm h12
  have hΓoff : ∀ i j, i ≠ j → Γ i j = 0 := by
    intro i j hij
    have h := congrFun (congrFun hΓD i) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at h
    have h' : (ν i - ν j) * Γ i j = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr (hνinj i j hij))
  obtain ⟨γ, hΓdiag⟩ : ∃ γ : Fin 3 → K, Γ = diagonal γ := ⟨fun i => Γ i i, by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij, hΓoff i j hij]⟩
  have hdetP : P.det ≠ 0 := by
    intro h
    have h1 := congrArg Matrix.det hPQ
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  have hγ0 : ∀ i, γ i ≠ 0 := by
    have hdΓ : Γ.det ≠ 0 := by
      rw [hΓ, Matrix.det_mul, det_conjTr]
      exact mul_ne_zero ((map_ne_zero σ).mpr hdetP) hdetP
    rw [hΓdiag, Matrix.det_diagonal, Fin.prod_univ_three] at hdΓ
    intro i
    fin_cases i
    · exact left_ne_zero_of_mul (left_ne_zero_of_mul hdΓ)
    · exact right_ne_zero_of_mul (left_ne_zero_of_mul hdΓ)
    · exact right_ne_zero_of_mul hdΓ
  have hΓstar : conjTr σ Γ = Γ := by
    rw [hΓ, conjTr_mul, conjTr_conjTr hσσ]
  have hγσ : ∀ i, σ (γ i) = γ i := by
    intro i
    have h := congrFun (congrFun hΓstar i) i
    rw [hΓdiag, conjTr_diagonal, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at h
    exact h
  have hnorm' : ∀ i, ∃ a : K, σ a * a = (γ i)⁻¹ := fun i =>
    hnorm _ (inv_ne_zero (hγ0 i)) (by rw [map_inv₀, hγσ])
  choose a ha using hnorm'
  obtain ⟨U, hUdef⟩ : ∃ U, U = P * diagonal a := ⟨_, rfl⟩
  have hUU : conjTr σ U * U = 1 := by
    rw [hUdef, conjTr_mul, conjTr_diagonal, Matrix.mul_assoc, ← Matrix.mul_assoc (conjTr σ P),
      ← hΓ, hΓdiag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    calc σ (a i) * (γ i * a i) = (σ (a i) * a i) * γ i := by ring
      _ = 1 := by rw [ha i, inv_mul_cancel₀ (hγ0 i)]
  have hUU' : U * conjTr σ U = 1 := mul_eq_one_comm.mp hUU
  have hXU : X * U = U * diagonal ν := by
    rw [hUdef, ← Matrix.mul_assoc, hXP, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal,
      Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    congr 2
    funext i
    exact mul_comm _ _
  obtain ⟨hl3, hl1⟩ := lambda_spec hν3 h01
  refine ⟨U * cyc3 K * conjTr σ U, ?_, ?_, ν 0 * (ν 1)⁻¹, hl3, hl1,
    conj_cyc3_mul hUU' hUU hXU hν3 hprod⟩
  · rw [Matrix.det_mul, Matrix.det_mul, det_cyc3, mul_one, mul_comm, ← Matrix.det_mul, hUU,
      Matrix.det_one]
  · have hcyc : conjTr σ (cyc3 K) = (cyc3 K)ᵀ := by
      rw [conjTr]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [cyc3]
    rw [conjTr_mul, conjTr_mul, conjTr_conjTr hσσ, hcyc]
    calc _ = U * ((cyc3 K)ᵀ * (conjTr σ U * U) * cyc3 K) * conjTr σ U := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hUU, Matrix.mul_one, cyc3_transpose_mul, Matrix.mul_one, hUU']

end Rot

end CFSG.RankThree.PartTwo.Sec4.Res424Seven
