module

import CFSG.Monster.Visible.AlgebraAction
public import CFSG.Monster.Parity.ShortLines
public import CFSG.Monster.Visible.Pair

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Parity

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.Griess CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible Matrix Module

theorem Lw_inA (A : symMat) (N : SpaceW) :
    Lw (inA A) N = N * MA (A : Matrix (Fin 24) (Fin 24) ℚ) := by
  rw [Lw_apply', MA]
  simp only [Am_inA, xs_inA, Pi.zero_apply, zero_smul, Finset.sum_const_zero, smul_zero, add_zero,
    Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
  exact add_comm _ _

theorem Lw_inX_smul_single (a : ℚ) (c : ShortIdx) (N : SpaceW) :
    Lw (inX (a • Pi.single c 1)) N = (a / 8) • (Rmat c * N * Kc c) := by
  rw [Lw_apply']
  simp only [Am_inX, trace_zero, zero_div, zero_smul, Matrix.mul_zero, zero_add, xs_inX]
  rw [sum_smul_single_smul, Kc, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
  module

theorem MA_conj {g : Matrix (Fin 24) (Fin 24) ℚ} (hg : g * gᵀ = 1)
    (A : Matrix (Fin 24) (Fin 24) ℚ) : MA (gᵀ * A * g) = gᵀ * MA A * g := by
  have hgt : gᵀ * g = 1 := mul_eq_one_comm.1 hg
  rw [MA, MA, trace_conj hg, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hgt]

theorem MA_surj (B : Matrix (Fin 24) (Fin 24) ℚ) :
    MA (B - (trace B / 32) • (1 : Matrix (Fin 24) (Fin 24) ℚ)) = B := by
  rw [MA, trace_sub, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]
  push_cast
  module

theorem bform_inW_inW (N N' : SpaceW) : bform (inW N) (inW N') = trace (Nᵀ * N') := by
  rw [bform_apply]
  change trace ((0 : Matrix (Fin 24) (Fin 24) ℚ) * 0) + ∑ c, (0 : SpaceX) c * (0 : SpaceX) c +
    ∑ j, ∑ i, N j i * N' j i = _
  rw [Griess.sum_sum_mul_eq_trace]
  simp

theorem Kc_mul_Kinv (c : ShortIdx) : Kc c * (1 - (28 : ℚ)⁻¹ • Umat c) = 1 := by
  simp only [Kc, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, Umat_mul_Umat, smul_smul]
  module

@[expose] def spinMat (f : SpaceB ≃ₗ[ℚ] SpaceB) (g : Matrix (Fin 24) (Fin 24) ℚ) :
    Matrix SpinIdx SpinIdx ℚ :=
  Matrix.of fun a b => (resW f (single a 0 1) * gᵀ) b 0

section SpinPart

variable {f : SpaceB ≃ₗ[ℚ] SpaceB} (hf : IsParityAut f) {g : latticeO}
  (hA : ∀ A : symMat, resA f A = thetaA (mat g) A)
include hf hA

theorem resW_mul_MA (A : symMat) (N : SpaceW) :
    resW f (N * MA (A : Matrix (Fin 24) (Fin 24) ℚ)) =
      resW f N * MA ((mat g)ᵀ * (A : Matrix (Fin 24) (Fin 24) ℚ) * mat g) := by
  have h := hf.resW_Lw (u := inA A) rfl N
  rw [Lw_inA, hf.apply_inA, hA, Lw_inA, coe_thetaA] at h
  exact h

theorem resW_mul_sym (B : Matrix (Fin 24) (Fin 24) ℚ) (hB : Bᵀ = B) (N : SpaceW) :
    resW f (N * B) * (mat g)ᵀ = resW f N * (mat g)ᵀ * B := by
  have hg := mat_mul_transpose g
  obtain ⟨A, hAB⟩ : ∃ A : symMat, MA (A : Matrix (Fin 24) (Fin 24) ℚ) = B :=
    ⟨⟨B - (trace B / 32) • (1 : Matrix (Fin 24) (Fin 24) ℚ), by
      rw [mem_symMat, transpose_sub, transpose_smul, transpose_one, hB]⟩, MA_surj B⟩
  have h := resW_mul_MA hf hA A N
  rw [hAB, MA_conj hg, hAB] at h
  rw [h]
  simp only [Matrix.mul_assoc, hg, Matrix.mul_one]

theorem resW_mul_single (N : SpaceW) (i j : Fin 24) :
    resW f (N * single i j (1 : ℚ)) * (mat g)ᵀ = resW f N * (mat g)ᵀ * single i j (1 : ℚ) := by
  by_cases hij : i = j
  · subst hij
    exact resW_mul_sym hf hA _ (transpose_single i i 1) N
  · have e : single i j (1 : ℚ) =
        single i i (1 : ℚ) * (single i j (1 : ℚ) + single j i (1 : ℚ)) := by
      simp [Matrix.mul_add, hij]
    have hF : (single i j (1 : ℚ) + single j i (1 : ℚ))ᵀ =
        single i j (1 : ℚ) + single j i (1 : ℚ) := by
      rw [transpose_add, transpose_single, transpose_single, add_comm]
    rw [e, ← Matrix.mul_assoc N, resW_mul_sym hf hA _ hF (N * single i i (1 : ℚ)),
      resW_mul_sym hf hA _ (transpose_single i i (1 : ℚ)) N,
      Matrix.mul_assoc _ (single i i (1 : ℚ))]

theorem resW_mul_transpose_eq (N : SpaceW) :
    resW f N * (mat g)ᵀ = (spinMat f (mat g))ᵀ * N := by
  have hlin : lr 1 (mat g)ᵀ ∘ₗ resW f = lr (spinMat f (mat g))ᵀ 1 := by
    refine (Matrix.stdBasis ℚ SpinIdx (Fin 24)).ext fun k => ?_
    obtain ⟨a, j⟩ := k
    rw [LinearMap.comp_apply, lr_apply, lr_apply, Matrix.stdBasis_eq_single, Matrix.one_mul,
      Matrix.mul_one]
    have h1 : resW f (single a j (1 : ℚ)) * (mat g)ᵀ =
        resW f (single a 0 (1 : ℚ)) * (mat g)ᵀ * single (0 : Fin 24) j (1 : ℚ) := by
      have := resW_mul_single hf hA (single a 0 1) 0 j
      rwa [single_mul_single_same, one_mul] at this
    rw [h1]
    ext b k
    by_cases hk : k = j
    · subst hk
      rw [mul_single_apply_same, mul_single_apply_same, mul_one, mul_one, transpose_apply,
        spinMat, of_apply]
    · rw [mul_single_apply_of_ne _ _ _ _ _ hk, mul_single_apply_of_ne _ _ _ _ _ hk]
  have := LinearMap.congr_fun hlin N
  rwa [LinearMap.comp_apply, lr_apply, lr_apply, Matrix.one_mul, Matrix.mul_one] at this

theorem resW_eq (N : SpaceW) : resW f N = (spinMat f (mat g))ᵀ * N * mat g := by
  have hgt : (mat g)ᵀ * mat g = 1 := mul_eq_one_comm.1 (mat_mul_transpose g)
  rw [← resW_mul_transpose_eq hf hA, Matrix.mul_assoc, hgt, Matrix.mul_one]

theorem spinMat_mul_transpose : spinMat f (mat g) * (spinMat f (mat g))ᵀ = 1 := by
  set s := spinMat f (mat g) with hs
  have hg := mat_mul_transpose g
  have key : ∀ N N' : SpaceW, trace (Nᵀ * (s * sᵀ) * N') = trace (Nᵀ * N') := by
    intro N N'
    have h := hf.map_bform (inW N) (inW N')
    rw [hf.apply_inW, hf.apply_inW, bform_inW_inW, bform_inW_inW, resW_eq hf hA,
      resW_eq hf hA] at h
    rw [← h]
    have e : (sᵀ * N * mat g)ᵀ * (sᵀ * N' * mat g) = (mat g)ᵀ * (Nᵀ * (s * sᵀ) * N') * mat g := by
      simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
    rw [e, trace_conj hg]
  ext a b
  have h := key (single a 0 1) (single b 0 1)
  rw [transpose_single, single_mul_mul_single, trace_single_eq_same, one_mul, mul_one] at h
  rw [h, one_apply]
  by_cases hab : a = b
  · subst hab
    rw [single_mul_single_same, trace_single_eq_same, mul_one, ite_eq_left rfl]
  · rw [single_mul_single_of_ne _ _ _ _ hab, trace_zero, ite_eq_right hab]

theorem spinMat_transpose_mul : (spinMat f (mat g))ᵀ * spinMat f (mat g) = 1 :=
  mul_eq_one_comm.1 (spinMat_mul_transpose hf hA)

end SpinPart

section Conj

variable {f : SpaceB ≃ₗ[ℚ] SpaceB} (hf : IsParityAut f) {g : latticeO}
  (hu : ∀ c : ShortIdx, uQ c ᵥ* mat g = uQ (hf.lineMap c) ∨ uQ c ᵥ* mat g = -uQ (hf.lineMap c))
include hu

theorem conj_Umat (c : ShortIdx) : (mat g)ᵀ * Umat c * mat g = Umat (hf.lineMap c) := by
  rw [Umat, mul_vecMulVec, mulVec_transpose, vecMulVec_mul, Umat]
  rcases hu c with h | h <;> rw [h]
  rw [neg_vecMulVec, vecMulVec_neg, neg_neg]

theorem Kc_mul_mat (c : ShortIdx) : Kc c * mat g = mat g * Kc (hf.lineMap c) := by
  have hg := mat_mul_transpose g
  have e : mat g * ((mat g)ᵀ * Umat c * mat g) = Umat c * mat g := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg, Matrix.one_mul]
  rw [Kc, Kc, ← conj_Umat hf hu c, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, e]

variable (hA : ∀ A : symMat, resA f A = thetaA (mat g) A)
include hA

theorem spin_conj_Rmat (c : ShortIdx) :
    (spinMat f (mat g))ᵀ * Rmat c * spinMat f (mat g) = hf.lineSign c • Rmat (hf.lineMap c) := by
  set s := spinMat f (mat g) with hs
  set d := hf.lineMap c with hd
  set ε := hf.lineSign c with hε
  have hK : ∀ N : SpaceW, resW f (Rmat c * N * Kc c) = ε • (Rmat d * resW f N * Kc d) := by
    intro N
    have h := hf.resW_Lw (u := inX (Pi.single c 1)) rfl N
    rw [hf.apply_inX, hf.resX_single] at h
    have e1 : Lw (inX (Pi.single c 1)) N = (8 : ℚ)⁻¹ • (Rmat c * N * Kc c) := by
      have := Lw_inX_smul_single 1 c N
      rw [one_smul] at this
      rw [this]
      norm_num
    rw [e1, Lw_inX_smul_single, map_smul] at h
    rw [show (ε / 8) • (Rmat d * resW f N * Kc d) = (8 : ℚ)⁻¹ • (ε • (Rmat d * resW f N * Kc d))
      by rw [smul_smul, div_eq_inv_mul]] at h
    exact smul_right_injective _ (by norm_num : (8 : ℚ)⁻¹ ≠ 0) h
  have hinv : mat g * Kc d * ((1 - (28 : ℚ)⁻¹ • Umat d) * (mat g)ᵀ) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Kc d), Kc_mul_Kinv, Matrix.one_mul,
      mat_mul_transpose]
  have hN : ∀ N : SpaceW, sᵀ * Rmat c * N = ε • (Rmat d * sᵀ) * N := by
    intro N
    have h := hK N
    rw [resW_eq hf hA, resW_eq hf hA] at h
    have h2 : sᵀ * Rmat c * N * (mat g * Kc d) = ε • (Rmat d * sᵀ) * N * (mat g * Kc d) := by
      calc sᵀ * Rmat c * N * (mat g * Kc d) = sᵀ * (Rmat c * N * Kc c) * mat g := by
            simp only [Matrix.mul_assoc]
            rw [Kc_mul_mat hf hu c]
        _ = ε • (Rmat d * (sᵀ * N * mat g) * Kc d) := h
        _ = ε • (Rmat d * sᵀ) * N * (mat g * Kc d) := by
            simp only [Matrix.mul_assoc, Matrix.smul_mul]
    calc sᵀ * Rmat c * N
        = sᵀ * Rmat c * N * (mat g * Kc d * ((1 - (28 : ℚ)⁻¹ • Umat d) * (mat g)ᵀ)) := by
          rw [hinv, Matrix.mul_one]
      _ = sᵀ * Rmat c * N * (mat g * Kc d) * ((1 - (28 : ℚ)⁻¹ • Umat d) * (mat g)ᵀ) := by
          rw [Matrix.mul_assoc (sᵀ * Rmat c * N)]
      _ = ε • (Rmat d * sᵀ) * N * (mat g * Kc d) * ((1 - (28 : ℚ)⁻¹ • Umat d) * (mat g)ᵀ) := by
          rw [h2]
      _ = ε • (Rmat d * sᵀ) * N := by
          rw [Matrix.mul_assoc (ε • (Rmat d * sᵀ) * N), hinv, Matrix.mul_one]
  have hP : sᵀ * Rmat c = ε • (Rmat d * sᵀ) := by
    ext a b
    have := congrFun (congrFun (hN (single b 0 1)) a) 0
    rwa [mul_single_apply_same, mul_single_apply_same, mul_one, mul_one] at this
  rw [hP, Matrix.smul_mul, Matrix.mul_assoc, spinMat_transpose_mul hf hA, Matrix.mul_one]

end Conj

end CFSG.Monster.Parity
