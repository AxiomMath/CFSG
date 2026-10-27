module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiDiag

public section

namespace CFSG.RankThree.PartTwo.Sec11

namespace KS11LieProof

open CFSG.RankThree.PartTwo.Sec4
open Matrix

variable {K : Type} [Field K]

theorem mul_self_eq_trace_smul_sub (M : Matrix (Fin 2) (Fin 2) K) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem det_sub_one_fin_two (M : Matrix (Fin 2) (Fin 2) K) :
    (M - 1).det = M.det - M.trace + 1 := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two]
  ring

theorem one_add_pow_of_sq_eq_zero {N : Matrix (Fin 2) (Fin 2) K} (hN : N * N = 0) (k : ℕ) :
    (1 + N) ^ k = 1 + (k : K) • N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, add_mul, one_mul, mul_add, mul_one, Matrix.smul_mul, hN, smul_zero,
      add_zero]
    push_cast
    rw [add_smul, one_smul]
    abel

theorem eq_one_of_det_sub_one_eq_zero {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det = 1)
    {n : ℕ} (hn : (n : K) ≠ 0) (hMn : M ^ n = 1) (h0 : (M - 1).det = 0) : M = 1 := by
  rw [det_sub_one_fin_two, hdet] at h0
  have ht : M.trace = 2 := by linear_combination -h0
  set N := M - 1 with hNdef
  have hN : N * N = 0 := by
    have hCH := mul_self_eq_trace_smul_sub M
    rw [ht, hdet] at hCH
    rw [hNdef, sub_mul, mul_sub, mul_sub, hCH, Matrix.mul_one, Matrix.one_mul, Matrix.one_mul]
    rw [two_smul, one_smul]
    abel
  have hM : M = 1 + N := by rw [hNdef]; abel
  rw [hM, one_add_pow_of_sq_eq_zero hN] at hMn
  have h1 : (n : K) • N = 0 := by
    have := congrArg (fun X => X - 1) hMn
    simpa using this
  have hN0 : N = 0 := by
    rcases smul_eq_zero.mp h1 with h | h
    · exact absurd h hn
    · exact h
  rw [hM, hN0, add_zero]

theorem det_sub_one_ne_zero {B : GL (Fin 2) K} (hdet : (B : Matrix (Fin 2) (Fin 2) K).det = 1)
    {n : ℕ} (hn : (n : K) ≠ 0) (hBn : B ^ n = 1) (hB1 : B ≠ 1) :
    ((B : Matrix (Fin 2) (Fin 2) K) - 1).det ≠ 0 := by
  intro h0
  apply hB1
  apply Units.ext
  refine eq_one_of_det_sub_one_eq_zero hdet hn ?_ h0
  rw [← Units.val_pow_eq_pow_val, hBn, Units.val_one]

theorem blockMat_sub (a a' : K) (B B' : Matrix (Fin 2) (Fin 2) K) :
    blockMat a B - blockMat a' B' = blockMat (a - a') (B - B') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat]

theorem blockMat_smul (c a : K) (B : Matrix (Fin 2) (Fin 2) K) :
    c • blockMat a B = blockMat (c * a) (c • B) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat]

theorem trace_blockMat (a : K) (B : Matrix (Fin 2) (Fin 2) K) :
    (blockMat a B).trace = a + B.trace := by
  simp [blockMat, Matrix.trace_fin_three, Matrix.trace_fin_two]
  ring

theorem coe_blockHom_of_det {B : GL (Fin 2) K} (hB : GeneralLinearGroup.det B = 1) :
    ((blockHom B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      blockMat 1 (B : Matrix (Fin 2) (Fin 2) K) := by
  rw [coe_blockHom, hB, inv_one, Units.val_one]

theorem det_pow_eq_one {B : GL (Fin 2) K} (hB : GeneralLinearGroup.det B = 1) (j : ℕ) :
    GeneralLinearGroup.det (B ^ j) = 1 := by
  rw [map_pow, hB, one_pow]

theorem matDet_eq_one {B : GL (Fin 2) K} (hB : GeneralLinearGroup.det B = 1) :
    (B : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  have := congrArg Units.val hB
  rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at this

theorem pow_three_eq_one_of_pow_three_mul {M : Type*} [Monoid M] {B : M} {k j : ℕ}
    (hBk : B ^ 3 ^ k = 1) (hj : j % 3 ≠ 0) (h : B ^ (3 * j) = 1) : B ^ 3 = 1 := by
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hBk)
  have h1 : 3 ^ i ∣ 3 * j := hi ▸ orderOf_dvd_of_pow_eq_one h
  rw [← orderOf_dvd_iff_pow_eq_one, hi]
  rcases i with _ | i
  · exact one_dvd _
  · rw [pow_succ', Nat.mul_dvd_mul_iff_left (by norm_num)] at h1
    rcases i with _ | i
    · exact dvd_refl _
    · exfalso
      rw [pow_succ'] at h1
      exact hj (Nat.mod_eq_zero_of_dvd (dvd_trans (dvd_mul_right 3 _) h1))

theorem eq_one_of_pow_eq_one_of_not_dvd {M : Type*} [Monoid M] {B : M} {k j : ℕ}
    (hBk : B ^ 3 ^ k = 1) (hj : j % 3 ≠ 0) (h : B ^ j = 1) : B = 1 := by
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hBk)
  have h1 : 3 ^ i ∣ j := hi ▸ orderOf_dvd_of_pow_eq_one h
  rcases i with _ | i
  · rw [pow_zero] at hi
    exact orderOf_eq_one_iff.mp hi
  · exfalso
    exact hj (Nat.mod_eq_zero_of_dvd (dvd_trans (dvd_pow_self 3 (by omega)) h1))

theorem commute_diagE_of_conj_eq {B : GL (Fin 2) K} (hBdet : GeneralLinearGroup.det B = 1)
    (h3 : (3 : K) ≠ 0) {k : ℕ} (hBk : B ^ 3 ^ k = 1) (hB3 : B ^ 3 ≠ 1)
    {S : GL (Fin 3) K} {ζ : Kˣ} {j : ℕ} (hj : j % 3 = 1)
    (hS : S * blockHom B * S⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * blockHom B ^ j)
    (e : Kˣ) : S * diagE e = diagE e * S := by
  have h3k : ((3 ^ k : ℕ) : K) ≠ 0 := by
    push_cast
    exact pow_ne_zero _ h3
  have hB1 : B ≠ 1 := by
    rintro rfl
    exact hB3 (one_pow 3)
  set Bm := (B : Matrix (Fin 2) (Fin 2) K) with hBm
  have hBmdet : Bm.det = 1 := matDet_eq_one hBdet
  have hBj : blockHom B ^ j = blockHom (B ^ j) := (map_pow blockHom B j).symm
  rw [hBj] at hS
  set Bj := B ^ j with hBjdef
  have hBjdet : GeneralLinearGroup.det Bj = 1 := det_pow_eq_one hBdet j
  set Sm := (S : Matrix (Fin 3) (Fin 3) K) with hSm
  set Sim := ((S⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hSim
  have hSS : Sm * Sim = 1 := by
    rw [hSm, hSim, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hSS' : Sim * Sm = 1 := by
    rw [hSm, hSim, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hSmat : Sm * blockMat 1 Bm * Sim = (ζ : K) • blockMat 1 (Bj : Matrix (Fin 2) (Fin 2) K) := by
    have := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K)) hS
    simp only [Units.val_mul, coe_blockHom_of_det hBdet, coe_blockHom_of_det hBjdet,
      GeneralLinearGroup.coe_scalar] at this
    rw [this, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
      Matrix.one_mul]
  have hconj : ∀ X : Matrix (Fin 3) (Fin 3) K, (Sm * X * Sim).det = X.det := by
    intro X
    rw [det_mul, det_mul, mul_comm (Sm.det), mul_assoc, ← det_mul, hSS, det_one, mul_one]
  have hconjsub : Sm * (blockMat 1 Bm - 1) * Sim = Sm * blockMat 1 Bm * Sim - 1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hSS]
  have hζ1 : (ζ : K) = 1 := by
    by_contra hζ
    have hdetD : (blockMat (1 : K) Bm).det = 1 := by rw [det_blockMat, hBmdet, one_mul]
    have hζ3 : (ζ : K) ^ 3 = 1 := by
      have := hconj (blockMat 1 Bm)
      rw [hSmat, Matrix.det_smul, det_blockMat, matDet_eq_one hBjdet, Fintype.card_fin,
        hdetD] at this
      simpa using this
    have h0 : (blockMat (1 : K) Bm - 1).det = 0 := by
      rw [← blockMat_one, blockMat_sub, sub_self, det_blockMat, zero_mul]
    have h0' : ((ζ : K) • blockMat 1 (Bj : Matrix (Fin 2) (Fin 2) K) - 1).det = 0 := by
      rw [← hSmat, ← hconjsub, hconj, h0]
    rw [blockMat_smul, mul_one, ← blockMat_one, blockMat_sub, det_blockMat] at h0'
    have hX : ((ζ : K) • (Bj : Matrix (Fin 2) (Fin 2) K) - 1).det = 0 :=
      (mul_eq_zero.mp h0').resolve_left (sub_ne_zero.mpr hζ)
    set X := (Bj : Matrix (Fin 2) (Fin 2) K) with hX'
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hX
    have hζ0 : (ζ : K) ≠ 0 := Units.ne_zero ζ
    have hXv : X *ᵥ v = (ζ : K)⁻¹ • v := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero, Matrix.smul_mulVec] at hv
      calc X *ᵥ v = (ζ : K)⁻¹ • ((ζ : K) • (X *ᵥ v)) := by
            rw [smul_smul, inv_mul_cancel₀ hζ0, one_smul]
        _ = (ζ : K)⁻¹ • v := by rw [hv]
    have hX3v : (X ^ 3 - 1) *ᵥ v = 0 := by
      have h1 : X ^ 3 *ᵥ v = v := by
        rw [pow_three, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        simp only [hXv, Matrix.mulVec_smul, smul_smul]
        rw [show (ζ : K)⁻¹ * (ζ : K)⁻¹ * (ζ : K)⁻¹ = ((ζ : K) ^ 3)⁻¹ by ring, hζ3, inv_one,
          one_smul]
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, h1, sub_self]
    have hX3 : (X ^ 3 - 1).det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, hX3v⟩
    have hX3det : (X ^ 3).det = 1 := by rw [det_pow, matDet_eq_one hBjdet, one_pow]
    have hX3k : (X ^ 3) ^ (3 ^ k) = 1 := by
      have hgl : ((B ^ j) ^ 3) ^ 3 ^ k = 1 := by
        rw [← pow_mul, ← pow_mul, show j * (3 * 3 ^ k) = 3 ^ k * (3 * j) by ring, pow_mul, hBk,
          one_pow]
      have := congrArg Units.val hgl
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_one] at this
      exact this
    have hX31 := eq_one_of_det_sub_one_eq_zero hX3det h3k hX3k hX3
    have hB3j : B ^ (3 * j) = 1 := by
      apply Units.ext
      rw [mul_comm, pow_mul, Units.val_pow_eq_pow_val, Units.val_one]
      exact hX31
    exact hB3 (pow_three_eq_one_of_pow_three_mul hBk (by omega) hB3j)
  have hSmat1 : Sm * blockMat 1 Bm * Sim = blockMat 1 (Bj : Matrix (Fin 2) (Fin 2) K) := by
    rw [hSmat, hζ1, one_smul]
  have htr : (Bj : Matrix (Fin 2) (Fin 2) K).trace = Bm.trace := by
    have h1 := congrArg Matrix.trace hSmat1
    rw [Matrix.trace_mul_cycle, hSS', Matrix.one_mul, trace_blockMat, trace_blockMat] at h1
    linear_combination -h1
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hBj1 : B ^ i = 1 := by
    set U := B ^ (i + 2) with hU
    set V := B ^ i with hV
    have hVBm : (V : Matrix (Fin 2) (Fin 2) K) * Bm = (Bj : Matrix (Fin 2) (Fin 2) K) := by
      rw [hV, hBjdef, pow_succ, Units.val_mul]
    have hCHB := mul_self_eq_trace_smul_sub Bm
    have hCHBj := mul_self_eq_trace_smul_sub (Bj : Matrix (Fin 2) (Fin 2) K)
    rw [hBmdet, one_smul] at hCHB
    rw [matDet_eq_one hBjdet, one_smul, htr] at hCHBj
    have hUV : (U : Matrix (Fin 2) (Fin 2) K) * (V : Matrix (Fin 2) (Fin 2) K) =
        (Bj : Matrix (Fin 2) (Fin 2) K) * (Bj : Matrix (Fin 2) (Fin 2) K) := by
      rw [← Units.val_mul, ← Units.val_mul, hU, hV, hBjdef, ← pow_add, ← pow_add]
      congr 2
      ring
    have hUeq : (U : Matrix (Fin 2) (Fin 2) K) = (V : Matrix (Fin 2) (Fin 2) K) * Bm * Bm := by
      rw [hU, hV, hBm, pow_succ, pow_succ, Units.val_mul, Units.val_mul]
    have hUpV : (U : Matrix (Fin 2) (Fin 2) K) + (V : Matrix (Fin 2) (Fin 2) K) =
        Bm.trace • (Bj : Matrix (Fin 2) (Fin 2) K) := by
      rw [hUeq, Matrix.mul_assoc, hCHB, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, hVBm]
      abel
    have hprod : ((U : Matrix (Fin 2) (Fin 2) K) - 1) * ((V : Matrix (Fin 2) (Fin 2) K) - 1) =
        0 := by
      calc ((U : Matrix (Fin 2) (Fin 2) K) - 1) * ((V : Matrix (Fin 2) (Fin 2) K) - 1) =
          (U : Matrix (Fin 2) (Fin 2) K) * (V : Matrix (Fin 2) (Fin 2) K) -
            ((U : Matrix (Fin 2) (Fin 2) K) + (V : Matrix (Fin 2) (Fin 2) K)) + 1 := by
            noncomm_ring
        _ = 0 := by rw [hUV, hUpV, hCHBj]; abel
    have hUinv : IsUnit ((U : Matrix (Fin 2) (Fin 2) K) - 1).det := by
      rw [isUnit_iff_ne_zero]
      refine det_sub_one_ne_zero (n := 3 ^ k) (matDet_eq_one (det_pow_eq_one hBdet _)) h3k ?_
        ?_
      · rw [hU, ← pow_mul, mul_comm, pow_mul, hBk, one_pow]
      · intro hU1
        apply hB1
        exact eq_one_of_pow_eq_one_of_not_dvd hBk (by omega) hU1
    have hV1 : (V : Matrix (Fin 2) (Fin 2) K) - 1 = 0 := by
      have := congrArg (((U : Matrix (Fin 2) (Fin 2) K) - 1)⁻¹ * ·) hprod
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hUinv] using this
    apply Units.ext
    rw [Units.val_one]
    exact sub_eq_zero.mp hV1
  have hBjB : (Bj : Matrix (Fin 2) (Fin 2) K) = Bm := by
    rw [hBjdef, pow_succ, hBj1, one_mul]
  have hcommS : Sm * blockMat 1 Bm = blockMat 1 Bm * Sm := by
    have h1 := congrArg (· * Sm) hSmat1
    rw [Matrix.mul_assoc, hSS', Matrix.mul_one, hBjB] at h1
    exact h1
  have hdet1 : (Bm - 1).det ≠ 0 :=
    det_sub_one_ne_zero hBmdet h3k hBk hB1
  rw [det_fin_two] at hdet1
  have hentry : ∀ a b, (Sm * blockMat 1 Bm) a b = (blockMat 1 Bm * Sm) a b :=
    fun a b => by rw [hcommS]
  have e01 := hentry 0 1
  have e02 := hentry 0 2
  have e10 := hentry 1 0
  have e20 := hentry 2 0
  simp [blockMat, Matrix.mul_apply, Fin.sum_univ_three] at e01 e02 e10 e20
  have s01 : Sm 0 1 = 0 := by
    have h : Sm 0 1 * ((Bm 0 0 - 1) * (Bm 1 1 - 1) - Bm 0 1 * Bm 1 0) = 0 := by
      linear_combination (Bm 1 1 - 1) * e01 - Bm 1 0 * e02
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd (by simpa [Matrix.sub_apply, Matrix.one_apply] using h) hdet1
  have s02 : Sm 0 2 = 0 := by
    have h : Sm 0 2 * ((Bm 0 0 - 1) * (Bm 1 1 - 1) - Bm 0 1 * Bm 1 0) = 0 := by
      linear_combination (Bm 0 0 - 1) * e02 - Bm 0 1 * e01
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd (by simpa [Matrix.sub_apply, Matrix.one_apply] using h) hdet1
  have s10 : Sm 1 0 = 0 := by
    have h : Sm 1 0 * ((Bm 0 0 - 1) * (Bm 1 1 - 1) - Bm 0 1 * Bm 1 0) = 0 := by
      linear_combination -(Bm 1 1 - 1) * e10 + Bm 0 1 * e20
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd (by simpa [Matrix.sub_apply, Matrix.one_apply] using h) hdet1
  have s20 : Sm 2 0 = 0 := by
    have h : Sm 2 0 * ((Bm 0 0 - 1) * (Bm 1 1 - 1) - Bm 0 1 * Bm 1 0) = 0 := by
      linear_combination -(Bm 0 0 - 1) * e20 + Bm 1 0 * e10
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd (by simpa [Matrix.sub_apply, Matrix.one_apply] using h) hdet1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagE, ← hSm]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_diagonal, Matrix.diagonal_mul, s01, s02, s10,
    s20, mul_comm]

end KS11LieProof

end CFSG.RankThree.PartTwo.Sec11
