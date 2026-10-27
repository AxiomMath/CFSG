module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
import CFSG.Mathlib.FieldTheory.Finite.QuadraticZero
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagExtension

public section

namespace CFSG.LocalAnalysis.WeakClosure81.PSpOuter

open Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  (IsTotallyIsotropic finrank_le_of_isTotallyIsotropic)

variable {r : ℕ} {k : Type} [Field k]

private lemma formJ_transpose : (formJ r k)ᵀ = -(formJ r k) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [formJ, Matrix.transpose_apply, Matrix.neg_apply, Matrix.one_apply, eq_comm]

private lemma formJ_mul_formJ :
    formJ r k * formJ r k = -(1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) := by
  simp only [formJ]
  rw [Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.one_apply]

private lemma neg_formJ_mul_formJ : (-(formJ r k)) * formJ r k = 1 := by
  rw [Matrix.neg_mul, formJ_mul_formJ, neg_neg]

private lemma formJ_det_ne_zero : (formJ r k).det ≠ 0 :=
  Matrix.det_ne_zero_of_left_inverse (neg_formJ_mul_formJ (r := r) (k := k))

private lemma formJ_bilin_nondegenerate : (Matrix.toBilin' (formJ r k)).Nondegenerate :=
  Matrix.nondegenerate_toBilin'_iff.mpr
    (Matrix.nondegenerate_of_det_ne_zero (formJ_det_ne_zero (r := r) (k := k)))

private lemma formJ_dot_self (h2 : (2 : k) ≠ 0) (u : Fin r ⊕ Fin r → k) :
    u ⬝ᵥ (formJ r k *ᵥ u) = 0 := by
  have h := Matrix.dotProduct_transpose_mulVec (formJ r k) u u
  rw [formJ_transpose, Matrix.neg_mulVec, dotProduct_neg] at h
  have h2' : (2 : k) * (u ⬝ᵥ (formJ r k *ᵥ u)) = 0 := by
    rw [two_mul]
    nth_rewrite 2 [← h]
    exact add_neg_cancel _
  exact (mul_eq_zero.mp h2').resolve_left h2

private lemma formJ_dot_swap (u v : Fin r ⊕ Fin r → k) :
    u ⬝ᵥ (formJ r k *ᵥ v) = -(v ⬝ᵥ (formJ r k *ᵥ u)) := by
  have h := Matrix.dotProduct_transpose_mulVec (formJ r k) u v
  rw [formJ_transpose, Matrix.neg_mulVec, dotProduct_neg] at h
  rw [← h, neg_neg]

private lemma exists_formJ_dot_ne_zero {u : Fin r ⊕ Fin r → k} (hu : u ≠ 0) :
    ∃ x, u ⬝ᵥ (formJ r k *ᵥ x) ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (funext fun i => by simpa using h i)
  refine ⟨-((formJ r k) *ᵥ Pi.single i 1), ?_⟩
  have hx : formJ r k *ᵥ -((formJ r k) *ᵥ Pi.single i 1) = Pi.single i 1 := by
    rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, formJ_mul_formJ, Matrix.neg_mulVec,
      neg_neg, Matrix.one_mulVec]
  rw [hx]
  have h1 : u ⬝ᵥ Pi.single i 1 = u i := by
    simp [dotProduct, Pi.single_apply]
  rw [h1]
  exact hi

private lemma vecMulVec_mul_vecMulVec_formJ (u v : Fin r ⊕ Fin r → k) :
    vecMulVec u (u ᵥ* formJ r k) * vecMulVec v (v ᵥ* formJ r k) =
      (u ⬝ᵥ (formJ r k *ᵥ v)) • vecMulVec u (v ᵥ* formJ r k) := by
  rw [Matrix.vecMulVec_mul_vecMulVec, ← Matrix.dotProduct_mulVec, Matrix.vecMulVec_smul]

private lemma vecMulVec_formJ_skew (z : Fin r ⊕ Fin r → k) :
    (vecMulVec z (z ᵥ* formJ r k))ᵀ * formJ r k +
      formJ r k * vecMulVec z (z ᵥ* formJ r k) = 0 := by
  have hneg : formJ r k *ᵥ z = -(z ᵥ* formJ r k) := by
    have h := Matrix.vecMul_transpose (formJ r k) z
    rw [formJ_transpose, Matrix.vecMul_neg] at h
    exact h.symm
  rw [Matrix.transpose_vecMulVec, Matrix.vecMulVec_mul, Matrix.mul_vecMulVec, hneg,
    Matrix.neg_vecMulVec, add_neg_cancel]

private lemma mul_vecMulVec_formJ {A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k} {ν : k}
    (hν : ν ≠ 0) (hA : Aᵀ * formJ r k * A = ν • formJ r k) (z : Fin r ⊕ Fin r → k) :
    A * vecMulVec z (z ᵥ* formJ r k) =
      ν⁻¹ • (vecMulVec (A *ᵥ z) ((A *ᵥ z) ᵥ* formJ r k) * A) := by
  have hw : ((A *ᵥ z) ᵥ* formJ r k) ᵥ* A = ν • (z ᵥ* formJ r k) := by
    rw [Matrix.vecMul_mulVec, Matrix.vecMul_vecMul, hA, Matrix.vecMul_smul]
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hw, Matrix.vecMulVec_smul, smul_smul,
    inv_mul_cancel₀ hν, one_smul]

private lemma formJ_mulVec_mulVec {A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k} {ν : k}
    (hA : Aᵀ * formJ r k * A = ν • formJ r k) (x y : Fin r ⊕ Fin r → k) :
    (A *ᵥ x) ⬝ᵥ (formJ r k *ᵥ (A *ᵥ y)) = ν * (x ⬝ᵥ (formJ r k *ᵥ y)) := by
  calc (A *ᵥ x) ⬝ᵥ (formJ r k *ᵥ (A *ᵥ y))
      = ((A *ᵥ x) ᵥ* formJ r k) ⬝ᵥ (A *ᵥ y) := Matrix.dotProduct_mulVec _ _ _
    _ = (x ᵥ* (Aᵀ * formJ r k)) ⬝ᵥ (A *ᵥ y) := by rw [Matrix.vecMul_mulVec]
    _ = ((x ᵥ* (Aᵀ * formJ r k)) ᵥ* A) ⬝ᵥ y := Matrix.dotProduct_mulVec _ _ _
    _ = (x ᵥ* (Aᵀ * formJ r k * A)) ⬝ᵥ y := by rw [Matrix.vecMul_vecMul]
    _ = (x ᵥ* (ν • formJ r k)) ⬝ᵥ y := by rw [hA]
    _ = ν • ((x ᵥ* formJ r k) ⬝ᵥ y) := by rw [Matrix.vecMul_smul, smul_dotProduct]
    _ = ν • (x ⬝ᵥ (formJ r k *ᵥ y)) := by rw [Matrix.dotProduct_mulVec]
    _ = ν * (x ⬝ᵥ (formJ r k *ᵥ y)) := by rw [smul_eq_mul]

private lemma N_props {A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k} {μ ν : k} (h2 : (2 : k) ≠ 0)
    (hν : ν ≠ 0) (hA : Aᵀ * formJ r k * A = ν • formJ r k) (hAA : A * A = μ • 1) (hμ : μ ≠ 0)
    {z : Fin r ⊕ Fin r → k}
    (hiso : z ⬝ᵥ (formJ r k *ᵥ (A *ᵥ z)) = 0) {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k}
    (hN : N = vecMulVec z (z ᵥ* formJ r k) + ν⁻¹ • vecMulVec (A *ᵥ z) ((A *ᵥ z) ᵥ* formJ r k)) :
    N * N = 0 ∧ A * N = N * A ∧ Nᵀ * formJ r k + formJ r k * N = 0 := by
  set Nz : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k := vecMulVec z (z ᵥ* formJ r k) with hNzdef
  set NAz : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k :=
    vecMulVec (A *ᵥ z) ((A *ᵥ z) ᵥ* formJ r k) with hNAzdef
  have hmain : N = Nz + ν⁻¹ • NAz := by rw [hN, hNzdef, hNAzdef]
  have hzz : Nz * Nz = 0 := by
    rw [hNzdef, vecMulVec_mul_vecMulVec_formJ, formJ_dot_self h2, zero_smul]
  have hzAz : Nz * NAz = 0 := by
    rw [hNzdef, hNAzdef, vecMulVec_mul_vecMulVec_formJ, hiso, zero_smul]
  have hAzz : NAz * Nz = 0 := by
    rw [hNzdef, hNAzdef, vecMulVec_mul_vecMulVec_formJ, formJ_dot_swap, hiso, neg_zero,
      zero_smul]
  have hAzAz : NAz * NAz = 0 := by
    rw [hNAzdef, vecMulVec_mul_vecMulVec_formJ, formJ_dot_self h2, zero_smul]
  have hsq0 : N * N = 0 := by
    rw [hmain]
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_add,
      Matrix.mul_smul, hzz, hzAz, hAzz, hAzAz]
    simp
  have hstep1 : A * Nz = ν⁻¹ • (NAz * A) := by
    rw [hNzdef, hNAzdef]
    exact mul_vecMulVec_formJ hν hA z
  have hstep2 : A * NAz =
      ν⁻¹ • (vecMulVec (A *ᵥ (A *ᵥ z)) ((A *ᵥ (A *ᵥ z)) ᵥ* formJ r k) * A) := by
    rw [hNAzdef]
    exact mul_vecMulVec_formJ hν hA (A *ᵥ z)
  have hdouble : A * (A * Nz) = μ • Nz := by
    rw [← Matrix.mul_assoc, hAA, Matrix.smul_mul, Matrix.one_mul]
  have hdouble' : A * (A * Nz) =
      (ν⁻¹ * (ν⁻¹ * μ)) • vecMulVec (A *ᵥ (A *ᵥ z)) ((A *ᵥ (A *ᵥ z)) ᵥ* formJ r k) := by
    calc A * (A * Nz) = A * (ν⁻¹ • (NAz * A)) := by rw [hstep1]
      _ = ν⁻¹ • (A * (NAz * A)) := by rw [Matrix.mul_smul]
      _ = ν⁻¹ • ((A * NAz) * A) := by rw [Matrix.mul_assoc]
      _ = ν⁻¹ • ((ν⁻¹ • (vecMulVec (A *ᵥ (A *ᵥ z)) ((A *ᵥ (A *ᵥ z)) ᵥ* formJ r k) * A)) * A) := by
            rw [hstep2]
      _ = ν⁻¹ • (ν⁻¹ • ((vecMulVec (A *ᵥ (A *ᵥ z)) ((A *ᵥ (A *ᵥ z)) ᵥ* formJ r k) * A) * A)) := by
            rw [Matrix.smul_mul]
      _ = ν⁻¹ • (ν⁻¹ • (vecMulVec (A *ᵥ (A *ᵥ z)) ((A *ᵥ (A *ᵥ z)) ᵥ* formJ r k) * (A * A))) := by
            rw [Matrix.mul_assoc]
      _ = ν⁻¹ • (ν⁻¹ • (vecMulVec (A *ᵥ (A *ᵥ z)) ((A *ᵥ (A *ᵥ z)) ᵥ* formJ r k) * (μ • 1))) := by
            rw [hAA]
      _ = ν⁻¹ • (ν⁻¹ • (μ • (vecMulVec (A *ᵥ (A *ᵥ z)) ((A *ᵥ (A *ᵥ z)) ᵥ* formJ r k) * 1))) := by
            rw [Matrix.mul_smul]
      _ = ν⁻¹ • (ν⁻¹ • (μ • vecMulVec (A *ᵥ (A *ᵥ z)) ((A *ᵥ (A *ᵥ z)) ᵥ* formJ r k))) := by
            rw [Matrix.mul_one]
      _ = (ν⁻¹ * (ν⁻¹ * μ)) • vecMulVec (A *ᵥ (A *ᵥ z)) ((A *ᵥ (A *ᵥ z)) ᵥ* formJ r k) := by
            rw [smul_smul, smul_smul, mul_assoc]
  have hNzA : Nz * A = (ν⁻¹ * ν⁻¹) •
      (vecMulVec (A *ᵥ (A *ᵥ z)) ((A *ᵥ (A *ᵥ z)) ᵥ* formJ r k) * A) := by
    have h : μ • (Nz * A) = (ν⁻¹ * (ν⁻¹ * μ)) •
        (vecMulVec (A *ᵥ (A *ᵥ z)) ((A *ᵥ (A *ᵥ z)) ᵥ* formJ r k) * A) := by
      have h' := congrArg (fun M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k => M * A)
        (hdouble.symm.trans hdouble')
      simpa [Matrix.smul_mul] using h'
    have h2' : μ • (Nz * A) = μ • ((ν⁻¹ * ν⁻¹) •
        (vecMulVec (A *ᵥ (A *ᵥ z)) ((A *ᵥ (A *ᵥ z)) ᵥ* formJ r k) * A)) := by
      rw [h, smul_smul]
      congr 1
      ring
    have := congrArg (fun M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k => μ⁻¹ • M) h2'
    simpa [smul_smul, hμ] using this
  have hcomm : A * N = N * A := by
    rw [hmain]
    calc A * (Nz + ν⁻¹ • NAz) = A * Nz + ν⁻¹ • (A * NAz) := by
          rw [Matrix.mul_add, Matrix.mul_smul]
      _ = ν⁻¹ • (NAz * A) + ν⁻¹ • (ν⁻¹ •
            (vecMulVec (A *ᵥ (A *ᵥ z)) ((A *ᵥ (A *ᵥ z)) ᵥ* formJ r k) * A)) := by
            rw [hstep1, hstep2]
      _ = ν⁻¹ • (NAz * A) + (ν⁻¹ * ν⁻¹) •
            (vecMulVec (A *ᵥ (A *ᵥ z)) ((A *ᵥ (A *ᵥ z)) ᵥ* formJ r k) * A) := by rw [smul_smul]
      _ = ν⁻¹ • (NAz * A) + Nz * A := by rw [← hNzA]
      _ = (Nz + ν⁻¹ • NAz) * A := by
            rw [Matrix.add_mul, Matrix.smul_mul]
            exact add_comm _ _
  refine ⟨hsq0, hcomm, ?_⟩
  have h1 : Nzᵀ * formJ r k + formJ r k * Nz = 0 := by
    rw [hNzdef]
    exact vecMulVec_formJ_skew z
  have h2' : NAzᵀ * formJ r k + formJ r k * NAz = 0 := by
    rw [hNAzdef]
    exact vecMulVec_formJ_skew (A *ᵥ z)
  have hsum : Nᵀ * formJ r k + formJ r k * N =
      (Nzᵀ * formJ r k + formJ r k * Nz) + ν⁻¹ • (NAzᵀ * formJ r k + formJ r k * NAz) := by
    rw [hmain, Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul, Matrix.smul_mul,
      Matrix.mul_add, Matrix.mul_smul, smul_add]
    abel
  rw [hsum, h1, h2', smul_zero, add_zero]

private lemma N_ne_zero_of_indep {A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k} {ν : k}
    {z : Fin r ⊕ Fin r → k} (hz : z ≠ 0)
    (hind : LinearIndependent k ![z, A *ᵥ z]) {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k}
    (hN : N = vecMulVec z (z ᵥ* formJ r k) + ν⁻¹ • vecMulVec (A *ᵥ z) ((A *ᵥ z) ᵥ* formJ r k)) :
    N ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_formJ_dot_ne_zero hz
  intro hzero
  have h0 : (vecMulVec z (z ᵥ* formJ r k) + ν⁻¹ •
      vecMulVec (A *ᵥ z) ((A *ᵥ z) ᵥ* formJ r k)) *ᵥ x = 0 := by
    rw [← hN, hzero, Matrix.zero_mulVec]
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec,
    op_smul_eq_smul, op_smul_eq_smul, ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec,
    smul_smul] at h0
  have hp := (LinearIndependent.pair_iff.mp hind) (z ⬝ᵥ (formJ r k *ᵥ x))
    (ν⁻¹ * ((A *ᵥ z) ⬝ᵥ (formJ r k *ᵥ x))) h0
  exact hx hp.1

private lemma N_ne_zero_of_eigen {A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k} {μ ν c : k}
    (h2 : (2 : k) ≠ 0) (hν : ν ≠ 0) (hνμ : ν = μ) (hAA : A * A = μ • 1)
    {z : Fin r ⊕ Fin r → k} (hz : z ≠ 0) (hc : A *ᵥ z = c • z)
    {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k}
    (hN : N = vecMulVec z (z ᵥ* formJ r k) + ν⁻¹ • vecMulVec (A *ᵥ z) ((A *ᵥ z) ᵥ* formJ r k)) :
    N ≠ 0 := by
  have hc2 : c * c = μ := by
    have h1 : A *ᵥ (A *ᵥ z) = (c * c) • z := by rw [hc, Matrix.mulVec_smul, hc, smul_smul]
    have h2' : A *ᵥ (A *ᵥ z) = μ • z := by
      rw [Matrix.mulVec_mulVec, hAA, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [h1] at h2'
    have h3 : (c * c - μ) • z = 0 := by rw [sub_smul, h2', sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hz)
  have hNz0 : vecMulVec z (z ᵥ* formJ r k) ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := exists_formJ_dot_ne_zero hz
    have h1 : vecMulVec z (z ᵥ* formJ r k) *ᵥ x = 0 := by rw [h0, Matrix.zero_mulVec]
    rw [Matrix.vecMulVec_mulVec, op_smul_eq_smul, ← Matrix.dotProduct_mulVec] at h1
    exact hx ((smul_eq_zero.mp h1).resolve_right hz)
  have hNAz : vecMulVec (A *ᵥ z) ((A *ᵥ z) ᵥ* formJ r k) =
      (c * c) • vecMulVec z (z ᵥ* formJ r k) := by
    rw [hc, Matrix.smul_vecMul, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul]
  have hval : N = (2 : k) • vecMulVec z (z ᵥ* formJ r k) := by
    have hμ : μ ≠ 0 := by rw [← hνμ]; exact hν
    calc N = vecMulVec z (z ᵥ* formJ r k) + ν⁻¹ •
          vecMulVec (A *ᵥ z) ((A *ᵥ z) ᵥ* formJ r k) := hN
      _ = vecMulVec z (z ᵥ* formJ r k) + ν⁻¹ •
          ((c * c) • vecMulVec z (z ᵥ* formJ r k)) := by rw [hNAz]
      _ = vecMulVec z (z ᵥ* formJ r k) + (ν⁻¹ * (c * c)) • vecMulVec z (z ᵥ* formJ r k) := by
            rw [smul_smul]
      _ = vecMulVec z (z ᵥ* formJ r k) + (1 : k) • vecMulVec z (z ᵥ* formJ r k) := by
            rw [hc2, hνμ, inv_mul_cancel₀ hμ]
      _ = vecMulVec z (z ᵥ* formJ r k) + vecMulVec z (z ᵥ* formJ r k) := by rw [one_smul]
      _ = (2 : k) • vecMulVec z (z ᵥ* formJ r k) := by rw [two_smul]
  intro hzero
  have h2z : (2 : k) • vecMulVec z (z ᵥ* formJ r k) = 0 := by rw [← hval, hzero]
  exact hNz0 ((smul_eq_zero.mp h2z).resolve_left h2)

private lemma sub_smul_one_mul_add_smul_one {A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k}
    {s : k} (hAA : A * A = (s * s) • 1) : (A - s • 1) * (A + s • 1) = 0 := by
  simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.one_mul, hAA]
  module

private lemma add_smul_one_mul_sub_smul_one {A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k}
    {s : k} (hAA : A * A = (s * s) • 1) : (A + s • 1) * (A - s • 1) = 0 := by
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.one_mul, hAA]
  module

private lemma exists_eigenvector {A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k} {s : k}
    (hAA : A * A = (s * s) • 1) (hs : A ≠ (-s) • 1) :
    ∃ e : Fin r ⊕ Fin r → k, e ≠ 0 ∧ A *ᵥ e = s • e := by
  classical
  by_contra h
  push Not at h
  have hfac : (A - s • 1) * (A + s • 1) = 0 := sub_smul_one_mul_add_smul_one hAA
  have hplus : A + s • 1 = 0 := by
    apply Matrix.ext_of_mulVec_single
    intro i
    rw [Matrix.zero_mulVec]
    have h1 : (A - s • 1) *ᵥ ((A + s • 1) *ᵥ Pi.single i 1) = 0 := by
      rw [Matrix.mulVec_mulVec, hfac, Matrix.zero_mulVec]
    have hv : A *ᵥ ((A + s • 1) *ᵥ Pi.single i 1) = s • ((A + s • 1) *ᵥ Pi.single i 1) := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h1
      exact h1
    by_contra h2
    exact h _ h2 hv
  refine hs ?_
  rw [neg_smul, eq_neg_iff_add_eq_zero]
  exact hplus

private lemma formJ_dot_add_sub (h2 : (2 : k) ≠ 0) {e f : Fin r ⊕ Fin r → k}
    (hef : e ⬝ᵥ (formJ r k *ᵥ f) = 0) :
    (e + f) ⬝ᵥ (formJ r k *ᵥ (e - f)) = 0 := by
  rw [Matrix.mulVec_sub, dotProduct_sub, add_dotProduct, add_dotProduct, formJ_dot_self h2,
    formJ_dot_swap f e, hef, formJ_dot_self h2]
  ring

private lemma independent_add_of_eigen (h2 : (2 : k) ≠ 0)
    {A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k}
    {s : k} {e f : Fin r ⊕ Fin r → k} (he0 : e ≠ 0) (hf0 : f ≠ 0) (hs0 : s ≠ 0)
    (he : A *ᵥ e = s • e) (hf : A *ᵥ f = -s • f) :
    LinearIndependent k ![(e + f), A *ᵥ (e + f)] := by
  have hAz : A *ᵥ (e + f) = s • (e - f) := by
    rw [Matrix.mulVec_add, he, hf, smul_sub, neg_smul, sub_eq_add_neg]
  have hLIef : LinearIndependent k ![e, f] := by
    rw [LinearIndependent.pair_iff' he0]
    intro a ha
    have h1 : A *ᵥ (a • e) = (a * s) • e := by rw [Matrix.mulVec_smul, he, smul_smul]
    have h2' : A *ᵥ (a • e) = A *ᵥ f := by rw [ha]
    have h3 : (a * s) • e = -s • f := by rw [← h1, h2', hf]
    have h4 : (a * s) • e = s • f := by rw [mul_comm a s, mul_smul, ha]
    have h3' : (a * s) • e = -(s • f) := by rw [h3, neg_smul]
    have h5 : s • f = -(s • f) := by
      calc s • f = (a * s) • e := h4.symm
        _ = -(s • f) := h3'
    have h6 : (2 : k) • (s • f) = 0 := by
      rw [two_smul]
      exact (eq_neg_iff_add_eq_zero).mp h5
    exact hf0 ((smul_eq_zero.mp ((smul_eq_zero.mp h6).resolve_left h2)).resolve_left hs0)
  rw [hAz, LinearIndependent.pair_iff]
  intro a b hab
  have h1 : (a + b * s) • e + (a - b * s) • f = 0 := by
    rw [add_smul, sub_smul]
    have hh := hab
    rw [smul_add, smul_sub, smul_sub, smul_smul, smul_smul] at hh
    linear_combination hh
  obtain ⟨h2', h3'⟩ := (LinearIndependent.pair_iff.mp hLIef) (a + b * s) (a - b * s) h1
  constructor
  · have h2a : (2 : k) * a = 0 := by linear_combination h2' + h3'
    exact (mul_eq_zero.mp h2a).resolve_left h2
  · have h2bs : (2 : k) * (b * s) = 0 := by linear_combination h2' - h3'
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h2bs).resolve_left h2)).resolve_right hs0

private lemma exists_orthogonal_eigen (h2 : (2 : k) ≠ 0) (hr : 2 ≤ r)
    {A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k} {μ ν s : k}
    (hA : Aᵀ * formJ r k * A = ν • formJ r k) (hAA : A * A = μ • 1) (hνμ : ν = -μ)
    (hs : μ = s * s) (hμ : μ ≠ 0)
    {e : Fin r ⊕ Fin r → k} (he : A *ᵥ e = s • e) :
    ∃ f : Fin r ⊕ Fin r → k, f ≠ 0 ∧ A *ᵥ f = -s • f ∧ e ⬝ᵥ (formJ r k *ᵥ f) = 0 := by
  classical
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    exact hμ hs
  have hAAs : A * A = (s * s) • 1 := by rw [hAA, hs]
  have hfac : (A - s • 1) * (A + s • 1) = 0 := sub_smul_one_mul_add_smul_one hAAs
  have hfac' : (A + s • 1) * (A - s • 1) = 0 := add_smul_one_mul_sub_smul_one hAAs
  let B : LinearMap.BilinForm k (Fin r ⊕ Fin r → k) := Matrix.toBilin' (formJ r k)
  have hBapp : ∀ x y : Fin r ⊕ Fin r → k, B x y = x ⬝ᵥ (formJ r k *ᵥ y) :=
    fun x y => Matrix.toBilin'_apply' _ _ _
  have hBalt : B.IsAlt := fun x => by rw [hBapp]; exact formJ_dot_self h2 x
  have hBnd : B.Nondegenerate := formJ_bilin_nondegenerate
  have hfr : Module.finrank k (Fin r ⊕ Fin r → k) = 2 * r := by
    rw [Module.finrank_pi k, Fintype.card_sum, Fintype.card_fin]
    omega
  let Vp : Submodule k (Fin r ⊕ Fin r → k) := LinearMap.ker ((A - s • 1).mulVecLin)
  let Vm : Submodule k (Fin r ⊕ Fin r → k) := LinearMap.ker ((A + s • 1).mulVecLin)
  have hVp : ∀ x, x ∈ Vp ↔ A *ᵥ x = s • x := by
    intro x
    rw [show Vp = LinearMap.ker ((A - s • 1).mulVecLin) from rfl, LinearMap.mem_ker,
      Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      sub_eq_zero]
  have hVm : ∀ x, x ∈ Vm ↔ A *ᵥ x = -s • x := by
    intro x
    rw [show Vm = LinearMap.ker ((A + s • 1).mulVecLin) from rfl, LinearMap.mem_ker,
      Matrix.mulVecLin_apply, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      add_eq_zero_iff_eq_neg, neg_smul]
  have hPiso : IsTotallyIsotropic B Vp := by
    intro x hx y hy
    rw [hBapp]
    have hx' : A *ᵥ x = s • x := (hVp x).mp hx
    have hy' : A *ᵥ y = s • y := (hVp y).mp hy
    have h := formJ_mulVec_mulVec hA x y
    rw [hx', hy'] at h
    have hL : (s • x) ⬝ᵥ (formJ r k *ᵥ (s • y)) = μ * (x ⬝ᵥ (formJ r k *ᵥ y)) := by
      rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_smul, ← hs, smul_eq_mul]
    rw [hL, hνμ, neg_mul] at h
    have h2' : (2 : k) * (μ * (x ⬝ᵥ (formJ r k *ᵥ y))) = 0 := by
      rw [two_mul]
      nth_rewrite 2 [h]
      exact add_neg_cancel _
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h2').resolve_left h2)).resolve_left hμ
  have hMiso : IsTotallyIsotropic B Vm := by
    intro x hx y hy
    rw [hBapp]
    have hx' : A *ᵥ x = -s • x := (hVm x).mp hx
    have hy' : A *ᵥ y = -s • y := (hVm y).mp hy
    have h := formJ_mulVec_mulVec hA x y
    rw [hx', hy'] at h
    have hL : (-s • x) ⬝ᵥ (formJ r k *ᵥ (-s • y)) = μ * (x ⬝ᵥ (formJ r k *ᵥ y)) := by
      rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_smul, neg_mul_neg, ← hs,
        smul_eq_mul]
    rw [hL, hνμ, neg_mul] at h
    have h2' : (2 : k) * (μ * (x ⬝ᵥ (formJ r k *ᵥ y))) = 0 := by
      rw [two_mul]
      nth_rewrite 2 [h]
      exact add_neg_cancel _
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h2').resolve_left h2)).resolve_left hμ
  have hPle : Module.finrank k Vp ≤ r := finrank_le_of_isTotallyIsotropic hBalt hBnd hfr hPiso
  have hrange : ((A + s • 1).mulVecLin).range ≤ Vp := by
    rintro y ⟨x, rfl⟩
    rw [hVp, Matrix.mulVecLin_apply]
    have hmul : A * (A + s • 1) = (s * s) • 1 + s • A := by
      rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, hAAs]
    calc A *ᵥ ((A + s • 1) *ᵥ x)
        = (A * (A + s • 1)) *ᵥ x := by rw [Matrix.mulVec_mulVec]
      _ = ((s * s) • 1 + s • A) *ᵥ x := by rw [hmul]
      _ = (s * s) • x + s • (A *ᵥ x) := by
            rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
      _ = s • (A *ᵥ x) + (s * s) • x := by rw [add_comm]
      _ = s • (A *ᵥ x + (s • 1) *ᵥ x) := by
            rw [Matrix.smul_mulVec, Matrix.one_mulVec, smul_add, smul_smul]
      _ = s • ((A + s • 1) *ᵥ x) := by rw [Matrix.add_mulVec]
  have hrange_le : Module.finrank k ↥((A + s • 1).mulVecLin).range ≤ r :=
    le_trans (Submodule.finrank_mono hrange) hPle
  have hrn : Module.finrank k ↥((A + s • 1).mulVecLin).range + Module.finrank k Vm = 2 * r := by
    have h := LinearMap.finrank_range_add_finrank_ker ((A + s • 1).mulVecLin)
    rw [show LinearMap.ker ((A + s • 1).mulVecLin) = Vm from rfl, hfr] at h
    omega
  have hVm2 : 2 ≤ Module.finrank k Vm := by omega
  have hVm_ne : Vm ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hVm2
    omega
  obtain ⟨f1, hf1m, hf1ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVm_ne
  have hf2 : ∃ f2 : Fin r ⊕ Fin r → k, f2 ∈ Vm ∧ f2 ∉ Submodule.span k {f1} := by
    by_contra hc
    push Not at hc
    have hle : Vm ≤ Submodule.span k ({f1} : Set (Fin r ⊕ Fin r → k)) := hc
    have h1 := Submodule.finrank_mono hle
    rw [finrank_span_singleton hf1ne] at h1
    omega
  obtain ⟨f2, hf2m, hf2s⟩ := hf2
  by_cases hzero : e ⬝ᵥ (formJ r k *ᵥ f1) = 0
  · exact ⟨f1, hf1ne, (hVm f1).mp hf1m, hzero⟩
  · have hf := (hVm f2).mp hf2m
    have hf1' := (hVm f1).mp hf1m
    refine ⟨(e ⬝ᵥ (formJ r k *ᵥ f1)) • f2 - (e ⬝ᵥ (formJ r k *ᵥ f2)) • f1, ?_, ?_, ?_⟩
    · intro hzero'
      have h1 : (e ⬝ᵥ (formJ r k *ᵥ f1)) • f2 = (e ⬝ᵥ (formJ r k *ᵥ f2)) • f1 := by
        rw [sub_eq_zero] at hzero'
        exact hzero'
      apply hf2s
      have h2'' : f2 = ((e ⬝ᵥ (formJ r k *ᵥ f1))⁻¹ * (e ⬝ᵥ (formJ r k *ᵥ f2))) • f1 := by
        have h3 := congrArg (fun w => (e ⬝ᵥ (formJ r k *ᵥ f1))⁻¹ • w) h1
        simpa [smul_smul, inv_mul_cancel₀ hzero] using h3
      rw [h2'']
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self f1)
    · rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hf, hf1']
      module
    · rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_sub,
        dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      ring

theorem exists_sq_zero_commute_gsp {k : Type} [Field k] [Finite k] (hk : ringChar k ≠ 2)
    {r : ℕ} (hr : 2 ≤ r) {A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k} {μ ν : k} (hν : ν ≠ 0)
    (hA : Aᵀ * formJ r k * A = ν • formJ r k) (hAA : A * A = μ • 1)
    (hAs : ∀ d : k, A ≠ d • 1) :
    ∃ N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k, N ≠ 0 ∧ N * N = 0 ∧ A * N = N * A ∧
      Nᵀ * formJ r k + formJ r k * N = 0 := by
  classical
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  have hpos : 0 < Fintype.card (Fin r ⊕ Fin r) := by
    rw [Fintype.card_sum, Fintype.card_fin]
    omega
  have hdetA : A.det ≠ 0 := by
    intro h0
    have h := congrArg Matrix.det hA
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, h0] at h
    have hz : (0 : k) = ν ^ Fintype.card (Fin r ⊕ Fin r) * (formJ r k).det := by simpa using h
    exact (mul_ne_zero (pow_ne_zero _ hν) (formJ_det_ne_zero (r := r) (k := k))) hz.symm
  have hμ : μ ≠ 0 := by
    intro h0
    have h := congrArg Matrix.det hAA
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, h0,
      zero_pow (Nat.pos_iff_ne_zero.mp hpos), mul_one] at h
    rcases mul_eq_zero.mp h with h1 | h1
    exacts [hdetA h1, hdetA h1]
  have hμν : μ * μ = ν * ν := by
    have h1 : (A * A)ᵀ * formJ r k * (A * A) = (ν * ν) • formJ r k := by
      calc (A * A)ᵀ * formJ r k * (A * A) = (Aᵀ * Aᵀ) * formJ r k * (A * A) := by
            rw [Matrix.transpose_mul]
        _ = Aᵀ * (Aᵀ * formJ r k * A) * A := by simp only [Matrix.mul_assoc]
        _ = Aᵀ * (ν • formJ r k) * A := by rw [hA]
        _ = ν • (Aᵀ * formJ r k * A) := by rw [Matrix.mul_smul, Matrix.smul_mul]
        _ = ν • (ν • formJ r k) := by rw [hA]
        _ = (ν * ν) • formJ r k := by rw [smul_smul]
    have h2' : (μ * μ) • formJ r k = (A * A)ᵀ * formJ r k * (A * A) := by
      rw [hAA, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
        Matrix.mul_smul, Matrix.mul_one, smul_smul]
    have h := congrFun (congrFun (h2'.trans h1) (Sum.inl ⟨0, by omega⟩))
      (Sum.inr ⟨0, by omega⟩)
    simpa [formJ, Matrix.fromBlocks_apply₁₂, Matrix.one_apply] using h
  have hAδ : Aᵀ * formJ r k = (ν * μ⁻¹) • (formJ r k * A) := by
    have h := congrArg (fun M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k => M * (μ⁻¹ • A)) hA
    rw [Matrix.mul_smul, Matrix.mul_assoc, hAA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul] at h
    simpa [smul_smul, inv_mul_cancel₀ hμ, one_smul] using h
  have hmul : ν = μ ∨ ν = -μ := by
    have h' : (ν - μ) * (ν + μ) = 0 := by
      have hsub : ν * ν - μ * μ = 0 := sub_eq_zero.mpr hμν.symm
      calc (ν - μ) * (ν + μ) = ν * ν - μ * μ := by ring
        _ = 0 := hsub
    rcases mul_eq_zero.mp h' with hc | hc
    · exact Or.inl (sub_eq_zero.mp hc)
    · exact Or.inr (by linear_combination hc)
  rcases hmul with hcase | hcase
  ·
    have hAtJ : Aᵀ * formJ r k = formJ r k * A := by
      rw [hAδ, hcase, mul_inv_cancel₀ hμ, one_smul]
    obtain ⟨z, hz⟩ : ∃ z : Fin r ⊕ Fin r → k, z ≠ 0 := by
      refine ⟨Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : k), ?_⟩
      intro h
      have h1 := congrFun h (Sum.inl (⟨0, by omega⟩ : Fin r))
      simp at h1
    have hiso : z ⬝ᵥ (formJ r k *ᵥ (A *ᵥ z)) = 0 := by
      have hsym : (A *ᵥ z) ⬝ᵥ (formJ r k *ᵥ z) = z ⬝ᵥ (formJ r k *ᵥ (A *ᵥ z)) := by
        calc (A *ᵥ z) ⬝ᵥ (formJ r k *ᵥ z)
            = ((A *ᵥ z) ᵥ* formJ r k) ⬝ᵥ z := Matrix.dotProduct_mulVec _ _ _
          _ = (z ᵥ* (Aᵀ * formJ r k)) ⬝ᵥ z := by rw [Matrix.vecMul_mulVec]
          _ = (z ᵥ* (formJ r k * A)) ⬝ᵥ z := by rw [hAtJ]
          _ = ((z ᵥ* formJ r k) ᵥ* A) ⬝ᵥ z := by rw [Matrix.vecMul_vecMul]
          _ = (z ᵥ* formJ r k) ⬝ᵥ (A *ᵥ z) := by rw [← Matrix.dotProduct_mulVec]
          _ = z ⬝ᵥ (formJ r k *ᵥ (A *ᵥ z)) := by rw [← Matrix.dotProduct_mulVec]
      have hanti := formJ_dot_swap z (A *ᵥ z)
      rw [hsym] at hanti
      have h2' : (2 : k) * (z ⬝ᵥ (formJ r k *ᵥ (A *ᵥ z))) = 0 := by
        rw [two_mul]
        nth_rewrite 2 [hanti]
        exact add_neg_cancel _
      exact (mul_eq_zero.mp h2').resolve_left h2
    by_cases hind : LinearIndependent k ![z, A *ᵥ z]
    · set N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k :=
        vecMulVec z (z ᵥ* formJ r k) + ν⁻¹ • vecMulVec (A *ᵥ z) ((A *ᵥ z) ᵥ* formJ r k)
        with hNdef
      exact ⟨N, N_ne_zero_of_indep hz hind hNdef,
        (N_props h2 hν hA hAA hμ hiso hNdef).1,
        (N_props h2 hν hA hAA hμ hiso hNdef).2.1,
        (N_props h2 hν hA hAA hμ hiso hNdef).2.2⟩
    · have hdep : ∃ c : k, A *ᵥ z = c • z := by
        by_contra hc
        push Not at hc
        exact hind ((LinearIndependent.pair_iff' hz).mpr fun a ha => hc a ha.symm)
      obtain ⟨c, hc⟩ := hdep
      set N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k :=
        vecMulVec z (z ᵥ* formJ r k) + ν⁻¹ • vecMulVec (A *ᵥ z) ((A *ᵥ z) ᵥ* formJ r k)
        with hNdef
      exact ⟨N, N_ne_zero_of_eigen h2 hν hcase hAA hz hc hNdef,
        (N_props h2 hν hA hAA hμ hiso hNdef).1,
        (N_props h2 hν hA hAA hμ hiso hNdef).2.1,
        (N_props h2 hν hA hAA hμ hiso hNdef).2.2⟩
  · by_cases hsq : IsSquare μ
    ·
      obtain ⟨s, hs⟩ := hsq
      have hAAs : A * A = (s * s) • 1 := by rw [hAA, hs]
      obtain ⟨e, he0, he⟩ := exists_eigenvector hAAs (hAs (-s))
      obtain ⟨f, hf0, hf, horth⟩ := exists_orthogonal_eigen h2 hr hA hAA hcase hs hμ he
      have hAz : A *ᵥ (e + f) = s • (e - f) := by
        rw [Matrix.mulVec_add, he, hf]
        module
      have hind : LinearIndependent k ![(e + f), A *ᵥ (e + f)] :=
        independent_add_of_eigen h2 he0 hf0 (by
          rintro rfl
          rw [mul_zero] at hs
          exact hμ hs) he hf
      have hz : e + f ≠ 0 := by
        have := hind.ne_zero 0
        simpa using this
      have hiso : (e + f) ⬝ᵥ (formJ r k *ᵥ (A *ᵥ (e + f))) = 0 := by
        rw [hAz, Matrix.mulVec_smul, dotProduct_smul, formJ_dot_add_sub h2 horth, smul_zero]
      set N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k :=
        vecMulVec (e + f) ((e + f) ᵥ* formJ r k) +
          ν⁻¹ • vecMulVec (A *ᵥ (e + f)) ((A *ᵥ (e + f)) ᵥ* formJ r k) with hNdef
      exact ⟨N, N_ne_zero_of_indep hz hind hNdef,
        (N_props h2 hν hA hAA hμ hiso hNdef).1,
        (N_props h2 hν hA hAA hμ hiso hNdef).2.1,
        (N_props h2 hν hA hAA hμ hiso hNdef).2.2⟩
    ·
      have hcard : 3 ≤ Fintype.card (Fin r ⊕ Fin r) := by
        rw [Fintype.card_sum, Fintype.card_fin]
        omega
      obtain ⟨z, hz, hiso⟩ := CFSG.FiniteField.exists_ne_zero_dotProduct_mulVec_eq_zero
        (K := k) (σ := Fin r ⊕ Fin r) hcard (formJ r k * A)
      rw [← Matrix.mulVec_mulVec] at hiso
      have hind : LinearIndependent k ![z, A *ᵥ z] := by
        rw [LinearIndependent.pair_iff' hz]
        intro c hc
        have hcz : A *ᵥ z = c • z := hc.symm
        have hc2 : c * c = μ := by
          have h1 : A *ᵥ (A *ᵥ z) = (c * c) • z := by
            rw [hcz, Matrix.mulVec_smul, hcz, smul_smul]
          have h2' : A *ᵥ (A *ᵥ z) = μ • z := by
            rw [Matrix.mulVec_mulVec, hAA, Matrix.smul_mulVec, Matrix.one_mulVec]
          rw [h1] at h2'
          have h3 : (c * c - μ) • z = 0 := by rw [sub_smul, h2', sub_self]
          exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hz)
        exact hsq ⟨c, hc2.symm⟩
      set N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k :=
        vecMulVec z (z ᵥ* formJ r k) + ν⁻¹ • vecMulVec (A *ᵥ z) ((A *ᵥ z) ᵥ* formJ r k)
        with hNdef
      exact ⟨N, N_ne_zero_of_indep hz hind hNdef,
        (N_props h2 hν hA hAA hμ hiso hNdef).1,
        (N_props h2 hν hA hAA hμ hiso hNdef).2.1,
        (N_props h2 hν hA hAA hμ hiso hNdef).2.2⟩

end CFSG.LocalAnalysis.WeakClosure81.PSpOuter
