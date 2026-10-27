module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import CFSG.Mathlib.FieldTheory.Finite.QuadraticZero
import TauCeti.LinearAlgebra.Matrix.OneSubVecMulVec
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.FieldTheory.Finite.GaloisField
import TauCeti.Algebra.QuadraticAlgebra.NormTrace

public section

open Matrix LinearMap

namespace CFSG.LocalAnalysis.WeakClosure81.PSLOuter

variable {k : Type*} [Field k] [Finite k] {n : ℕ}

private theorem exists_sq_add_sq_of_finite_field (hk : ringChar k ≠ 2) (μ : k) :
    ∃ b s : k, b ^ 2 + s ^ 2 = μ := by
  classical
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  by_cases h : IsSquare (-1 : k)
  · obtain ⟨i, hi⟩ := h
    refine ⟨(μ + 1) / 2, i * (μ - 1) / 2, ?_⟩
    have hi2 : i ^ 2 = -1 := by rw [pow_two]; exact hi.symm
    field_simp
    ring_nf
    rw [hi2]
    ring
  · let hfact : Fact (∀ r : k, r ^ 2 ≠ (-1 : k) + 0 * r) := ⟨by
      intro r hr
      apply h
      refine ⟨r, ?_⟩
      have hr' : r * r = -1 := by
        rw [← pow_two]
        simpa using hr
      exact hr'.symm⟩
    let hfield : Field (QuadraticAlgebra k (-1 : k) 0) :=
      @QuadraticAlgebra.instField k _ (-1) 0 hfact
    let hfin : Finite (QuadraticAlgebra k (-1 : k) 0) :=
      Module.finite_of_finite k
    obtain ⟨y, hy⟩ := @FiniteField.norm_surjective k (QuadraticAlgebra k (-1 : k) 0)
      (inferInstance : Field k) hfield
      (inferInstance : Algebra k (QuadraticAlgebra k (-1 : k) 0)) hfin μ
    refine ⟨y.re, y.im, ?_⟩
    rw [QuadraticAlgebra.algebraNorm_eq_norm, QuadraticAlgebra.norm_def] at hy
    simpa [pow_two] using hy

omit [Finite k] in
private lemma reflection_isometry {Φ : Matrix (Fin n) (Fin n) k} (hΦt : Φᵀ = Φ)
    {x : Fin n → k} (hx : (Φ.toBilin') x x ≠ 0) :
    (1 - (2 / (Φ.toBilin') x x) • vecMulVec x (Φ *ᵥ x))ᵀ * Φ *
      (1 - (2 / (Φ.toBilin') x x) • vecMulVec x (Φ *ᵥ x)) = Φ := by
  classical
  set a : k := (Φ.toBilin') x x with ha
  set c : k := 2 / a with hc
  set u : Fin n → k := Φ *ᵥ x with hu
  have hux : u ⬝ᵥ x = a := by
    rw [hu, ha, Matrix.toBilin'_apply']
    exact dotProduct_comm (Φ *ᵥ x) x
  have hxΦ : x ᵥ* Φ = u := by
    simpa [hu, hΦt] using Matrix.vecMul_transpose Φ x
  have hMt : (vecMulVec x u)ᵀ = vecMulVec u x := Matrix.transpose_vecMulVec _ _
  have h1 : (vecMulVec x u)ᵀ * Φ = vecMulVec u u := by
    rw [hMt, Matrix.vecMulVec_mul, hxΦ]
  have h2 : Φ * vecMulVec x u = vecMulVec u u := by
    simpa [hu] using Matrix.mul_vecMulVec Φ x u
  have h3 : (vecMulVec x u)ᵀ * Φ * vecMulVec x u = a • vecMulVec u u := by
    rw [h1, Matrix.vecMulVec_mul_vecMulVec, hux, Matrix.vecMulVec_smul]
  have hc2 : c * (c * a) = 2 * c := by
    rw [hc]
    field_simp
  rw [show vecMulVec x (Φ *ᵥ x) = vecMulVec x u by rw [hu]]
  change (1 - c • vecMulVec x u)ᵀ * Φ * (1 - c • vecMulVec x u) = Φ
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hMt]
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_one,
    Matrix.mul_smul]
  rw [← hMt]
  rw [h1, h2]
  rw [Matrix.vecMulVec_mul_vecMulVec, hux, Matrix.vecMulVec_smul]
  rw [smul_sub]
  simp only [smul_smul]
  rw [hc2]
  module

omit [Finite k] in
private lemma reflection_det {Φ : Matrix (Fin n) (Fin n) k} (_hΦt : Φᵀ = Φ)
    {x : Fin n → k} (hx : (Φ.toBilin') x x ≠ 0) :
    (1 - (2 / (Φ.toBilin') x x) • vecMulVec x (Φ *ᵥ x)).det = -1 := by
  classical
  set a : k := (Φ.toBilin') x x with ha
  set c : k := 2 / a with hc
  set u : Fin n → k := Φ *ᵥ x with hu
  have hux : u ⬝ᵥ x = a := by
    rw [hu, ha, Matrix.toBilin'_apply']
    exact dotProduct_comm (Φ *ᵥ x) x
  have hcx : c • x = (2 / a) • x := by rw [hc]
  rw [show x = x by rfl]
  rw [show (2 / (Φ.toBilin') x x) • vecMulVec x (Φ *ᵥ x) =
      vecMulVec (c • x) u by
    rw [hcx, hu, Matrix.smul_vecMulVec]]
  rw [TauCeti.det_one_sub_vecMulVec]
  rw [dotProduct_smul, hux]
  rw [hc, smul_eq_mul]
  rw [div_mul_cancel₀]
  · ring
  · exact hx

omit [Finite k] in
private lemma reflection_mulVec {Φ : Matrix (Fin n) (Fin n) k} (hΦt : Φᵀ = Φ)
    {x : Fin n → k} (_hx : (Φ.toBilin') x x ≠ 0) (v : Fin n → k) :
    (1 - (2 / (Φ.toBilin') x x) • vecMulVec x (Φ *ᵥ x)) *ᵥ v =
      v - ((2 / (Φ.toBilin') x x) * (Φ.toBilin') x v) • x := by
  classical
  set a : k := (Φ.toBilin') x x with ha
  set c : k := 2 / a with hc
  set u : Fin n → k := Φ *ᵥ x with hu
  have hxΦ : x ᵥ* Φ = u := by
    simpa [hu, hΦt] using Matrix.vecMul_transpose Φ x
  have hB : (Φ.toBilin') x v = u ⬝ᵥ v := by
    rw [Matrix.toBilin'_apply', Matrix.dotProduct_mulVec, hxΦ]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
  rw [hB, op_smul_eq_smul, smul_smul]

theorem orth_conj_or_inverted_unipotent_of_not_sq (hk : ringChar k ≠ 2) {n : ℕ}
    (hn : 3 ≤ n) {A Φ : Matrix (Fin n) (Fin n) k} {μ : k}
    (hΦ : IsUnit Φ.det) (hΦt : Φᵀ = Φ) (hA2 : A * A = μ • 1) (hμ : ¬ IsSquare μ)
    (hAΦ : Aᵀ * Φ = Φ * A) :
    (∃ g : Matrix (Fin n) (Fin n) k, gᵀ * Φ * g = Φ ∧ g.det = 1 ∧
        g * A * g⁻¹ * A = A * (g * A * g⁻¹) ∧ ∀ c : k, g * A * g⁻¹ ≠ c • A) ∨
      ∃ Y : Matrix (Fin n) (Fin n) k, Y ≠ 1 ∧ (Y - 1) ^ 3 = 0 ∧ Yᵀ * Φ * Y = Φ ∧
        A * Y * A⁻¹ = Y⁻¹ := by
  classical
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  have hμ0 : μ ≠ 0 := by
    intro h0
    exact hμ ⟨0, by rw [h0]; ring⟩
  have hΦ0 : Φ.det ≠ 0 := hΦ.ne_zero
  have hAunit : IsUnit A.det := by
    rw [isUnit_iff_ne_zero]
    intro hAdet
    have h : A.det * A.det = μ ^ n := by
      rw [← Matrix.det_mul, hA2, Matrix.det_smul, Matrix.det_one, Fintype.card_fin]
      simp
    rw [hAdet, zero_mul] at h
    exact hμ0 (pow_eq_zero_iff'.mp h.symm).1
  let B : LinearMap.BilinForm k (Fin n → k) := Φ.toBilin'
  have hBsymm : B.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr hΦt
  have hBrefl : B.IsRefl := hBsymm.isRefl
  have hBnd : B.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hΦ0
  have hAdj : ∀ w v : Fin n → k, B w (A.mulVec v) = B (A.mulVec w) v := by
    intro w v
    have hBdef : B = Φ.toBilin' := rfl
    rw [hBdef, Matrix.toBilin'_apply', Matrix.toBilin'_apply']
    calc
      w ⬝ᵥ Φ.mulVec (A.mulVec v) = w ⬝ᵥ (Φ * A).mulVec v := by
        rw [← Matrix.mulVec_mulVec]
      _ = w ⬝ᵥ (Aᵀ * Φ).mulVec v := by rw [hAΦ]
      _ = (w ᵥ* (Aᵀ * Φ)) ⬝ᵥ v := Matrix.dotProduct_mulVec w (Aᵀ * Φ) v
      _ = ((A.mulVec w) ᵥ* Φ) ⬝ᵥ v := by rw [← Matrix.vecMul_mulVec]
      _ = (A.mulVec w) ⬝ᵥ Φ.mulVec v := (Matrix.dotProduct_mulVec (A.mulVec w) Φ v).symm
  obtain ⟨b, s, hbs⟩ := exists_sq_add_sq_of_finite_field hk μ
  have hs : s ≠ 0 := by
    intro hs0
    apply hμ
    refine ⟨b, ?_⟩
    rw [← hbs, hs0, pow_two]
    ring
  let M : Matrix (Fin n) (Fin n) k := Φ * (A - b • 1)
  obtain ⟨z, hz0, hz⟩ :=
    CFSG.FiniteField.exists_ne_zero_dotProduct_mulVec_eq_zero (K := k) (σ := Fin n)
      (by simpa using hn) M
  have hzM : M.mulVec z = Φ.mulVec (A.mulVec z) - b • (Φ.mulVec z) := by
    change (Φ * (A - b • 1)).mulVec z = Φ.mulVec (A.mulVec z) - b • Φ.mulVec z
    rw [← Matrix.mulVec_mulVec]
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
  have hzβ : B z (A *ᵥ z) = b * B z z := by
    have h := hz
    rw [hzM] at h
    have hB1 : B z (A.mulVec z) = z ⬝ᵥ Φ.mulVec (A.mulVec z) := by
      have hBdef : B = Φ.toBilin' := rfl
      rw [hBdef]
      exact Matrix.toBilin'_apply' Φ z (A.mulVec z)
    have hB2 : B z z = z ⬝ᵥ Φ.mulVec z := by
      have hBdef : B = Φ.toBilin' := rfl
      rw [hBdef]
      exact Matrix.toBilin'_apply' Φ z z
    rw [hB1, hB2]
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul] at h
    exact sub_eq_zero.mp h
  let u : Fin n → k := A *ᵥ z
  let a : k := B z z
  have hzz : B z z = a := rfl
  have hzu : B z u = b * a := by
    show B z (A *ᵥ z) = b * B z z
    exact hzβ
  have huz : B u z = b * a := by
    rw [hBsymm.eq, hzu]
  have hAu : A *ᵥ u = μ • z := by
    show A.mulVec (A.mulVec z) = μ • z
    rw [Matrix.mulVec_mulVec, hA2, Matrix.smul_mulVec, Matrix.one_mulVec]
  have huu : B u u = μ * a := by
    dsimp only [u, a]
    calc
      B (A.mulVec z) (A.mulVec z) = B (A.mulVec (A.mulVec z)) z := hAdj (A.mulVec z) z
      _ = B (μ • z) z := by rw [hAu]
      _ = μ * B z z := by rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hLI : LinearIndependent k ![z, u] := by
    rw [LinearIndependent.pair_iff' hz0]
    intro c hc
    have hc' : A *ᵥ z = c • z := by
      show A *ᵥ z = c • z
      exact hc.symm
    have h' : A *ᵥ u = (c * c) • z := by
      change A *ᵥ (A *ᵥ z) = (c * c) • z
      rw [hc', Matrix.mulVec_smul, hc', smul_smul]
    have h : μ • z = (c * c) • z := by
      rw [← hAu, h']
    have h0 : (μ - c * c) • z = 0 := by
      rw [sub_smul, h, sub_self]
    have hμc : μ = c * c := sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hz0)
    exact hμ ⟨c, hμc⟩
  by_cases ha : a = 0
  ·
    have hzz0 : B z z = 0 := by rw [hzz, ha]
    have hzu0 : B z u = 0 := by rw [hzu, ha, mul_zero]
    have huu0 : B u u = 0 := by rw [huu, ha, mul_zero]
    have huz0 : B u z = 0 := by rw [hBsymm.eq, hzu0]
    let T : Matrix (Fin n) (Fin n) k := vecMulVec z u - vecMulVec u z
    let N : Matrix (Fin n) (Fin n) k := T * Φ
    have hNm : ∀ w : Fin n → k, N.mulVec w = B u w • z - B z w • u := by
      intro w
      dsimp only [N, T]
      rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec,
        Matrix.vecMulVec_mulVec, op_smul_eq_smul, op_smul_eq_smul]
      simp [B, Matrix.toBilin'_apply']
    have hN2 : N * N = 0 := by
      apply Matrix.ext_of_mulVec_single
      intro i
      rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
      change N.mulVec (N.mulVec (Pi.single i 1)) = 0
      have h1 : B u (N.mulVec (Pi.single i 1)) = 0 := by
        rw [hNm]
        simp [map_sub, map_smul, huz0, huu0, smul_eq_mul]
      have h2 : B z (N.mulVec (Pi.single i 1)) = 0 := by
        rw [hNm]
        simp [map_sub, map_smul, hzz0, hzu0, smul_eq_mul]
      rw [hNm, h1, h2, zero_smul, zero_smul, sub_zero]
    have hTne : T ≠ 0 := by
      intro hT
      have hTu : ∀ i j, z i * u j = u i * z j := by
        intro i j
        have := congrFun (congrFun hT i) j
        exact sub_eq_zero.mp (by
          simpa [T, Matrix.sub_apply, Matrix.vecMulVec_apply] using this)
      obtain ⟨i0, hi0⟩ : ∃ i0, z i0 ≠ 0 := by
        by_contra h
        push Not at h
        exact hz0 (funext h)
      let c : k := u i0 / z i0
      have hu : u = c • z := by
        funext j
        have h := hTu i0 j
        have h' : u j = (u i0 / z i0) * z j := by
          field_simp [hi0]
          simpa [mul_comm] using h
        simpa [c] using h'
      exact (LinearIndependent.pair_iff' hz0).mp hLI c hu.symm
    have hNne : N ≠ 0 := by
      intro hN
      apply hTne
      have h := congrArg (fun M : Matrix (Fin n) (Fin n) k => M * Φ⁻¹) hN
      simpa [N, Matrix.mul_assoc, Matrix.mul_nonsing_inv Φ hΦ] using h
    have hTΦT : T * Φ * T = 0 := by
      have h := congrArg (fun M : Matrix (Fin n) (Fin n) k => M * Φ⁻¹) hN2
      simpa [N, Matrix.mul_assoc, Matrix.mul_nonsing_inv Φ hΦ] using h
    let Y : Matrix (Fin n) (Fin n) k := 1 + N
    have hYne : Y ≠ 1 := by
      intro hY
      apply hNne
      have h : 1 + N = 1 + 0 := by simpa [Y] using hY
      exact add_left_cancel h
    have hY3 : (Y - 1) ^ 3 = 0 := by
      have hYsub : Y - 1 = N := by
        change (1 + N) - 1 = N
        abel
      rw [hYsub]
      rw [show N ^ 3 = N ^ 2 * N by rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ]]
      rw [show N ^ 2 = N * N by rw [pow_two], hN2, zero_mul]
    have hTt : Tᵀ = -T := by
      change (vecMulVec z u - vecMulVec u z)ᵀ = -(vecMulVec z u - vecMulVec u z)
      rw [Matrix.transpose_sub, Matrix.transpose_vecMulVec, Matrix.transpose_vecMulVec]
      abel
    have hNt : Nᵀ = -(Φ * T) := by
      change (T * Φ)ᵀ = -(Φ * T)
      rw [Matrix.transpose_mul, hΦt, hTt, Matrix.mul_neg]
    have hYΦ : Yᵀ * Φ * Y = Φ := by
      have hYtrans : Yᵀ = 1 + Nᵀ := by
        change (1 + N)ᵀ = 1 + Nᵀ
        rw [Matrix.transpose_add, Matrix.transpose_one]
      rw [hYtrans, hNt]
      have h1 : (1 + -(Φ * T)) * Φ * (1 + T * Φ) =
          Φ - Φ * (T * Φ * T) * Φ := by
        noncomm_ring
      rw [h1, hTΦT]
      simp
    have hAT : A * T = -(T * Aᵀ) := by
      change A * (vecMulVec z u - vecMulVec u z) =
        -((vecMulVec z u - vecMulVec u z) * Aᵀ)
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec,
        Matrix.vecMulVec_mul, Matrix.vecMulVec_mul]
      rw [Matrix.vecMul_transpose, Matrix.vecMul_transpose]
      rw [show A.mulVec z = u from rfl, hAu, Matrix.smul_vecMulVec]
      rw [Matrix.vecMulVec_smul]
      abel
    have hAN : A * N = -(N * A) := by
      change A * (T * Φ) = -((T * Φ) * A)
      calc
        A * (T * Φ) = (A * T) * Φ := (Matrix.mul_assoc A T Φ).symm
        _ = (-(T * Aᵀ)) * Φ := by rw [hAT]
        _ = -(T * (Aᵀ * Φ)) := by rw [Matrix.neg_mul, Matrix.mul_assoc]
        _ = -(T * (Φ * A)) := by rw [hAΦ]
        _ = -((T * Φ) * A) := by rw [Matrix.mul_assoc]
    have hYinv : Y⁻¹ = 1 - N := by
      apply Matrix.inv_eq_right_inv
      change (1 + N) * (1 - N) = 1
      have h1 : (1 + N) * (1 - N) = 1 - N * N := by noncomm_ring
      rw [h1, hN2, sub_zero]
    have hAY : A * Y * A⁻¹ = Y⁻¹ := by
      calc
        A * Y * A⁻¹ = A * (1 + N) * A⁻¹ := by rw [show Y = 1 + N from rfl]
        _ = A * A⁻¹ + (A * N) * A⁻¹ := by noncomm_ring
        _ = 1 + (A * N) * A⁻¹ := by rw [Matrix.mul_nonsing_inv A hAunit]
        _ = 1 + (-(N * A)) * A⁻¹ := by rw [hAN]
        _ = 1 - N := by
          rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv A hAunit,
            Matrix.mul_one]
          abel
        _ = Y⁻¹ := by rw [hYinv]
    exact Or.inr ⟨Y, hYne, hY3, hYΦ, hAY⟩
  ·
    have ha' : a ≠ 0 := ha
    let W : Submodule k (Fin n → k) := Submodule.span k (Set.range ![z, u])
    have hWpair : W = Submodule.span k ({z, u} : Set (Fin n → k)) := by
      rw [show W = Submodule.span k (Set.range ![z, u]) from rfl]
      congr 1
      ext x
      simp [or_comm]
    have hWfin : Module.finrank k W = 2 := by
      rw [show W = Submodule.span k (Set.range ![z, u]) from rfl]
      simpa using finrank_span_eq_card hLI
    have hzW : z ∈ W := by
      rw [hWpair]
      exact Submodule.subset_span (by simp)
    have huW : u ∈ W := by
      rw [hWpair]
      exact Submodule.subset_span (by simp)
    have hWnd : (B.restrict W).Nondegenerate := by
      refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft ?_
      intro w hw
      apply Subtype.ext
      have hwW : (w : Fin n → k) ∈ Submodule.span k ({z, u} : Set (Fin n → k)) := by
        rw [← hWpair]
        exact w.2
      obtain ⟨α, β, hw'⟩ := Submodule.mem_span_pair.mp hwW
      have h1 : B (w : Fin n → k) z = 0 := by
        have := hw ⟨z, hzW⟩
        simpa [LinearMap.BilinForm.restrict_apply] using this
      have h2 : B (w : Fin n → k) u = 0 := by
        have := hw ⟨u, huW⟩
        simpa [LinearMap.BilinForm.restrict_apply] using this
      have huz : B u z = b * a := by
        have hBsymm : B.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr hΦt
        rw [hBsymm.eq, hzu]
      rw [← hw'] at h1 h2
      rw [map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.smul_apply, hzz, huz, smul_eq_mul] at h1
      rw [map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.smul_apply, hzu, huu, smul_eq_mul] at h2
      have hβ : β = 0 := by
        have hlin : a * ((b ^ 2 - μ) * β) = 0 := by
          linear_combination b * h1 - h2
        have hcomb : (b ^ 2 - μ) * β = 0 := (mul_eq_zero.mp hlin).resolve_left ha'
        rw [show b ^ 2 - μ = -s ^ 2 by linear_combination hbs] at hcomb
        have hs2 : s ^ 2 * β = 0 := by linear_combination -hcomb
        exact (mul_eq_zero.mp hs2).resolve_left (pow_ne_zero 2 hs)
      have hα : α = 0 := by
        have : α * a = 0 := by
          simpa [hβ] using h1
        exact (mul_eq_zero.mp this).resolve_right ha'
      rw [← hw', hα, hβ, zero_smul, zero_smul, add_zero]
      simp
    have hAW : ∀ w ∈ W, A.mulVec w ∈ W := by
      intro w hw
      have hw' : w ∈ Submodule.span k ({z, u} : Set (Fin n → k)) := by
        rwa [← hWpair]
      obtain ⟨α, β, hwβ⟩ := Submodule.mem_span_pair.mp hw'
      rw [← hwβ, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        show A.mulVec z = u from rfl, hAu]
      exact W.add_mem (W.smul_mem α huW) (W.smul_mem β (W.smul_mem μ hzW))
    let Wperp : Submodule k (Fin n → k) := B.orthogonal W
    have hAperp : ∀ v, v ∈ Wperp → A.mulVec v ∈ Wperp := by
      intro v hv
      have hv' : v ∈ B.orthogonal W := hv
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv' ⊢
      intro w hw
      rw [show B w (A.mulVec v) = B (A.mulVec w) v from hAdj w v]
      exact hv' (A.mulVec w) (hAW w hw)
    have hcompl : IsCompl W Wperp :=
      LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hBrefl hWnd
    have hdecomp : ∀ x : Fin n → k, ∃ w ∈ W, ∃ v ∈ Wperp, w + v = x := by
      intro x
      have hx : x ∈ W ⊔ Wperp := by
        rw [hcompl.sup_eq_top]
        exact Submodule.mem_top
      exact Submodule.mem_sup.mp hx
    let y : Fin n → k := u - (b + s) • z
    have hyz : B y z = -s * a := by
      dsimp only [y]
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hzz, huz,
        smul_eq_mul]
      ring
    have hyu : B y u = a * s * (s - b) := by
      dsimp only [y]
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hzu, huu,
        smul_eq_mul]
      rw [← hbs]
      ring
    have hyy : B y y = 2 * a * s ^ 2 := by
      dsimp only [y]
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hzz, hzu, huz,
        huu, smul_eq_mul]
      rw [← hbs]
      ring
    let rz : Matrix (Fin n) (Fin n) k :=
      1 - (2 / (Φ.toBilin') z z) • vecMulVec z (Φ *ᵥ z)
    have hzB : (Φ.toBilin') z z = a := hzz
    have hzB0 : (Φ.toBilin') z z ≠ 0 := by rw [hzB]; exact ha'
    have hrz_iso : rzᵀ * Φ * rz = Φ := by
      dsimp only [rz]
      exact reflection_isometry hΦt hzB0
    have hrz_det : rz.det = -1 := by
      dsimp only [rz]
      exact reflection_det hΦt hzB0
    have hrz_self : rz.mulVec z = -z := by
      dsimp only [rz]
      rw [reflection_mulVec hΦt hzB0 z, hzB]
      rw [show (2 / a) * a = 2 by field_simp]
      module
    have hrz_u : rz.mulVec u = u - (2 * b) • z := by
      dsimp only [rz]
      rw [reflection_mulVec hΦt hzB0 u, hzB, hzu]
      rw [show (2 / a) * (b * a) = 2 * b by field_simp]
    have hzy : B z y = -s * a := by rw [hBsymm.eq, hyz]
    have hrz_y : rz.mulVec y = u + (s - b) • z := by
      dsimp only [rz]
      rw [reflection_mulVec hΦt hzB0 y, hzB, hzy]
      rw [show (2 / a) * (-s * a) = -2 * s by field_simp]
      dsimp only [y]
      module
    let ry : Matrix (Fin n) (Fin n) k :=
      1 - (2 / (Φ.toBilin') y y) • vecMulVec y (Φ *ᵥ y)
    have hyB : (Φ.toBilin') y y = 2 * a * s ^ 2 := hyy
    have hyB0 : (Φ.toBilin') y y ≠ 0 := by
      rw [hyB]
      exact mul_ne_zero (mul_ne_zero h2 ha') (pow_ne_zero 2 hs)
    have hry_iso : ryᵀ * Φ * ry = Φ := by
      dsimp only [ry]
      exact reflection_isometry hΦt hyB0
    have hry_det : ry.det = -1 := by
      dsimp only [ry]
      exact reflection_det hΦt hyB0
    have hry_self : ry.mulVec y = -y := by
      dsimp only [ry]
      rw [reflection_mulVec hΦt hyB0 y, hyB]
      rw [show (2 / (2 * a * s ^ 2)) * (2 * a * s ^ 2) = 2 by field_simp]
      module
    have hry_z : ry.mulVec z = z + (1 / s) • y := by
      dsimp only [ry]
      rw [reflection_mulVec hΦt hyB0 z, hyB, hyz]
      rw [show (2 / (2 * a * s ^ 2)) * (-s * a) = -1 / s by field_simp]
      module
    have hry_u : ry.mulVec u = u - ((s - b) / s) • y := by
      dsimp only [ry]
      rw [reflection_mulVec hΦt hyB0 u, hyB, hyu]
      rw [show (2 / (2 * a * s ^ 2)) * (a * s * (s - b)) = (s - b) / s by
        field_simp]
    let J : Matrix (Fin n) (Fin n) k := rz * ry
    have hJ_iso : Jᵀ * Φ * J = Φ := by
      calc
        Jᵀ * Φ * J = ryᵀ * (rzᵀ * Φ * rz) * ry := by
          change (rz * ry)ᵀ * Φ * (rz * ry) = ryᵀ * (rzᵀ * Φ * rz) * ry
          rw [Matrix.transpose_mul]
          noncomm_ring
        _ = ryᵀ * Φ * ry := by rw [hrz_iso]
        _ = Φ := hry_iso
    have hJ_det : J.det = 1 := by
      change (rz * ry).det = 1
      rw [Matrix.det_mul, hrz_det, hry_det]
      norm_num
    have hJz : J.mulVec z = (1 / s) • u - (b / s) • z := by
      change (rz * ry).mulVec z = (1 / s) • u - (b / s) • z
      rw [← Matrix.mulVec_mulVec]
      rw [hry_z, Matrix.mulVec_add, Matrix.mulVec_smul, hrz_self, hrz_y]
      simp only [div_eq_mul_inv, one_mul]
      rw [smul_add, smul_smul, mul_sub, inv_mul_cancel₀ hs]
      module
    have hJu : J.mulVec u = (b / s) • u - (μ / s) • z := by
      change (rz * ry).mulVec u = (b / s) • u - (μ / s) • z
      rw [← Matrix.mulVec_mulVec]
      rw [hry_u, Matrix.mulVec_sub, Matrix.mulVec_smul, hrz_u, hrz_y]
      simp only [div_eq_mul_inv]
      rw [smul_add, smul_smul]
      have hc1 : (s - b) * s⁻¹ = 1 - b * s⁻¹ := by
        rw [sub_mul, mul_inv_cancel₀ hs]
      have hc2 : (s - b) * (s - b) * s⁻¹ = s - 2 * b + b ^ 2 * s⁻¹ := by
        field_simp [hs]
        ring
      have hc2' : s - 2 * b + b ^ 2 * s⁻¹ = μ * s⁻¹ - 2 * b := by
        have hc4 : s + b ^ 2 * s⁻¹ = μ * s⁻¹ := by
          rw [← hbs]
          field_simp [hs]
          ring
        rw [← hc4]
        ring
      rw [show (s - b) * s⁻¹ * (s - b) = (s - b) * (s - b) * s⁻¹ by ring]
      rw [hc1, hc2, hc2']
      module
    have hJ2z : (J * J).mulVec z = -z := by
      rw [← Matrix.mulVec_mulVec]
      rw [hJz, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hJu, hJz]
      rw [← hbs]
      simp only [div_eq_mul_inv, one_mul, smul_sub, smul_smul]
      ring_nf
      rw [show s ^ 2 * s⁻¹ ^ 2 = 1 by rw [← mul_pow, mul_inv_cancel₀ hs, one_pow]]
      module
    have hJ2u : (J * J).mulVec u = -u := by
      rw [← Matrix.mulVec_mulVec]
      rw [hJu, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hJu, hJz]
      rw [← hbs]
      simp only [div_eq_mul_inv, one_mul, smul_sub, smul_smul]
      ring_nf
      rw [show s ^ 2 * s⁻¹ ^ 2 = 1 by rw [← mul_pow, mul_inv_cancel₀ hs, one_pow]]
      module
    have hJ2W : ∀ w ∈ W, (J * J).mulVec w = -w := by
      intro w hw
      have hw' : w ∈ Submodule.span k ({z, u} : Set (Fin n → k)) := by
        rwa [← hWpair]
      obtain ⟨α, β, hwβ⟩ := Submodule.mem_span_pair.mp hw'
      rw [← hwβ, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hJ2z, hJ2u]
      module
    have hyW : y ∈ W := by
      have h : y = u - (b + s) • z := rfl
      rw [h]
      exact W.sub_mem huW (W.smul_mem _ hzW)
    have hJperp : ∀ v ∈ Wperp, J.mulVec v = v := by
      intro v hv
      have hv' : v ∈ B.orthogonal W := hv
      have hzv : B z v = 0 :=
        (LinearMap.BilinForm.mem_orthogonal_iff.mp hv') z hzW
      have hyv : B y v = 0 :=
        (LinearMap.BilinForm.mem_orthogonal_iff.mp hv') y hyW
      have hrv : ry.mulVec v = v := by
        dsimp only [ry]
        rw [reflection_mulVec hΦt hyB0 v, hyv]
        simp
      have hrzv : rz.mulVec v = v := by
        dsimp only [rz]
        rw [reflection_mulVec hΦt hzB0 v, hzv]
        simp
      calc
        J.mulVec v = rz.mulVec (ry.mulVec v) := by
          change (rz * ry).mulVec v = rz.mulVec (ry.mulVec v)
          rw [← Matrix.mulVec_mulVec]
        _ = v := by rw [hrv, hrzv]
    have hJ2perp : ∀ v ∈ Wperp, (J * J).mulVec v = v := by
      intro v hv
      rw [← Matrix.mulVec_mulVec]
      rw [hJperp v hv, hJperp v hv]
    have hAJ2pt : ∀ x : Fin n → k,
        A.mulVec ((J * J).mulVec x) = (J * J).mulVec (A.mulVec x) := by
      intro x
      obtain ⟨w, hwW, v, hvW, hwv⟩ := hdecomp x
      rw [← hwv]
      calc
        A.mulVec ((J * J).mulVec (w + v)) = A.mulVec (-w + v) := by
          rw [Matrix.mulVec_add, hJ2W w hwW, hJ2perp v hvW]
        _ = -A.mulVec w + A.mulVec v := by
          rw [Matrix.mulVec_add, Matrix.mulVec_neg]
        _ = (J * J).mulVec (A.mulVec w + A.mulVec v) := by
          rw [Matrix.mulVec_add, hJ2W _ (hAW w hwW), hJ2perp _ (hAperp v hvW)]
        _ = (J * J).mulVec (A.mulVec (w + v)) := by
          simp only [Matrix.mulVec_add]
    have hAJ2 : A * (J * J) = (J * J) * A := by
      apply Matrix.ext_of_mulVec_single
      intro i
      calc
        (A * (J * J)).mulVec (Pi.single i 1) =
            A.mulVec ((J * J).mulVec (Pi.single i 1)) :=
          (Matrix.mulVec_mulVec (Pi.single i 1) A (J * J)).symm
        _ = (J * J).mulVec (A.mulVec (Pi.single i 1)) :=
          hAJ2pt (Pi.single i 1)
        _ = ((J * J) * A).mulVec (Pi.single i 1) :=
          Matrix.mulVec_mulVec (Pi.single i 1) (J * J) A
    have hJAz : J.mulVec (A.mulVec z) = -A.mulVec (J.mulVec z) := by
      rw [hJu, hJz, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
        hAu]
      change (b / s) • u - (μ / s) • z =
        -((1 / s) • (μ • z) - (b / s) • u)
      simp only [div_eq_mul_inv]
      module
    have hJAu : J.mulVec (A.mulVec u) = -A.mulVec (J.mulVec u) := by
      rw [hAu, Matrix.mulVec_smul, hJz, hJu, Matrix.mulVec_sub,
        Matrix.mulVec_smul, Matrix.mulVec_smul, hAu]
      change μ • ((1 / s) • u - (b / s) • z) =
        -((b / s) • (μ • z) - (μ / s) • u)
      simp only [div_eq_mul_inv]
      module
    have hAJz : A.mulVec (J.mulVec z) = -J.mulVec u := by
      simpa [u] using (congrArg (fun x => -x) hJAz).symm
    have hAJu : A.mulVec (J.mulVec u) = -J.mulVec (A.mulVec u) := by
      simpa [u] using (congrArg (fun x => -x) hJAu).symm
    have hJAW : ∀ w ∈ W, J.mulVec (A.mulVec w) = -A.mulVec (J.mulVec w) := by
      intro w hw
      have hw' : w ∈ Submodule.span k ({z, u} : Set (Fin n → k)) := by
        rwa [← hWpair]
      obtain ⟨α, β, hwβ⟩ := Submodule.mem_span_pair.mp hw'
      rw [← hwβ]
      conv_lhs =>
        rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
          show A.mulVec z = u from rfl, hAu,
          Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
          Matrix.mulVec_smul]
      conv_rhs =>
        rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
      rw [hAJz, hAJu, hAu, Matrix.mulVec_smul, hJz]
      module
    have hJ3W : ∀ w ∈ W, (J * J * J).mulVec w = -J.mulVec w := by
      intro w hw
      rw [show J * J * J = J * (J * J) by rw [Matrix.mul_assoc],
        ← Matrix.mulVec_mulVec, hJ2W w hw, Matrix.mulVec_neg]
    have hJ3perp : ∀ v ∈ Wperp, (J * J * J).mulVec v = v := by
      intro v hv
      rw [show J * J * J = J * (J * J) by rw [Matrix.mul_assoc],
        ← Matrix.mulVec_mulVec, hJ2perp v hv, hJperp v hv]
    have hJApt : ∀ x : Fin n → k,
        J.mulVec (A.mulVec x) = A.mulVec ((J * J * J).mulVec x) := by
      intro x
      obtain ⟨w, hwW, v, hvW, hwv⟩ := hdecomp x
      rw [← hwv]
      calc
        J.mulVec (A.mulVec (w + v)) =
            J.mulVec (A.mulVec w + A.mulVec v) := by rw [Matrix.mulVec_add]
        _ = J.mulVec (A.mulVec w) + J.mulVec (A.mulVec v) := by
          rw [Matrix.mulVec_add]
        _ = -A.mulVec (J.mulVec w) + A.mulVec v := by
          rw [hJAW w hwW, hJperp _ (hAperp v hvW)]
        _ = A.mulVec ((J * J * J).mulVec w) +
            A.mulVec ((J * J * J).mulVec v) := by
          rw [hJ3W w hwW, hJ3perp v hvW, Matrix.mulVec_neg]
        _ = A.mulVec ((J * J * J).mulVec (w + v)) := by
          simp only [Matrix.mulVec_add]
    have hJAm : J * A = A * (J * J * J) := by
      apply Matrix.ext_of_mulVec_single
      intro i
      calc
        (J * A).mulVec (Pi.single i 1) =
            J.mulVec (A.mulVec (Pi.single i 1)) :=
          (Matrix.mulVec_mulVec (Pi.single i 1) J A).symm
        _ = A.mulVec ((J * J * J).mulVec (Pi.single i 1)) :=
          hJApt (Pi.single i 1)
        _ = (A * (J * J * J)).mulVec (Pi.single i 1) :=
          Matrix.mulVec_mulVec (Pi.single i 1) A (J * J * J)
    have hJunit : IsUnit J.det := by
      rw [hJ_det]
      exact isUnit_one
    have hJinv : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hJunit
    have hA' : J * A * J⁻¹ = A * (J * J) := by
      calc
        J * A * J⁻¹ = (J * A) * J⁻¹ := by rw [Matrix.mul_assoc]
        _ = (A * (J * J * J)) * J⁻¹ := by rw [hJAm]
        _ = A * ((J * J * J) * J⁻¹) := by rw [Matrix.mul_assoc]
        _ = A * (J * J) := by
          rw [Matrix.mul_assoc, hJinv, Matrix.mul_one]
    have hcomm : (J * A * J⁻¹) * A = A * (J * A * J⁻¹) := by
      rw [hA', Matrix.mul_assoc, ← hAJ2]
    have hWne : W ≠ ⊤ := by
      intro htop
      have hfr : Module.finrank k W = n := by
        rw [htop, finrank_top, Module.finrank_fin_fun]
      rw [hWfin] at hfr
      omega
    have hWperp_ne : Wperp ≠ ⊥ := by
      intro hbot
      apply hWne
      have h := hcompl.sup_eq_top
      rw [hbot, sup_bot_eq] at h
      exact h
    refine Or.inl ⟨J, hJ_iso, hJ_det, hcomm, ?_⟩
    intro c hc
    have hJ2c : J * J = c • (1 : Matrix (Fin n) (Fin n) k) := by
      have h := hc
      rw [hA'] at h
      calc
        J * J = (A⁻¹ * A) * (J * J) := by
          rw [Matrix.nonsing_inv_mul A hAunit, Matrix.one_mul]
        _ = A⁻¹ * (A * (J * J)) := by rw [Matrix.mul_assoc]
        _ = A⁻¹ * (c • A) := by rw [h]
        _ = c • 1 := by
          rw [Matrix.mul_smul, Matrix.nonsing_inv_mul A hAunit]
    have hcneg : c = -1 := by
      have h1 : (J * J).mulVec z = (c • (1 : Matrix (Fin n) (Fin n) k)).mulVec z := by
        rw [hJ2c]
      rw [hJ2z, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
      have h2 : ((-1 : k) • z) = c • z := by
        rw [neg_one_smul]
        exact h1
      exact (smul_left_injective k hz0 h2).symm
    obtain ⟨v, hvperp, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWperp_ne
    have hv_eq : v = -v := by
      have h1 : (J * J).mulVec v = (c • (1 : Matrix (Fin n) (Fin n) k)).mulVec v := by
        rw [hJ2c]
      rw [hJ2perp v hvperp, Matrix.smul_mulVec, Matrix.one_mulVec, hcneg] at h1
      rwa [neg_one_smul] at h1
    have hv2 : (2 : k) • v = 0 := by
      rw [two_smul]
      nth_rewrite 1 [hv_eq]
      exact neg_add_cancel v
    have hvzero : v = 0 := (smul_eq_zero.mp hv2).resolve_left h2
    exact hv0 hvzero
end CFSG.LocalAnalysis.WeakClosure81.PSLOuter
