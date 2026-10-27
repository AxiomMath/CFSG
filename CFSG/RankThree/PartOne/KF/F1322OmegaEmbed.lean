module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartOne.KF1322

open Matrix

section Abstract

variable {K : Type*} [Field K] {M : Matrix (Fin 3) (Fin 3) K} {ι : Matrix (Fin 3) (Fin 2) K}
  {π : Matrix (Fin 2) (Fin 3) K}

@[expose] def emb (ι : Matrix (Fin 3) (Fin 2) K) (π : Matrix (Fin 2) (Fin 3) K)
    (R : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  1 + ι * (R - 1) * π

theorem emb_mul_aux (h1 : π * ι = 1) (A B : Matrix (Fin 2) (Fin 2) K) :
    (1 + ι * A * π) * (1 + ι * B * π) = 1 + ι * (A + B + A * B) * π := by
  have hX : ∀ X : Matrix (Fin 2) (Fin 3) K, π * (ι * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, hX]
  abel

theorem emb_mul (h1 : π * ι = 1) (R R' : Matrix (Fin 2) (Fin 2) K) :
    emb ι π R * emb ι π R' = emb ι π (R * R') := by
  unfold emb
  rw [emb_mul_aux h1]
  congr 3
  noncomm_ring

theorem emb_one : emb ι π (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  simp [emb]

theorem det_emb (h1 : π * ι = 1) (R : Matrix (Fin 2) (Fin 2) K) :
    (emb ι π R).det = R.det := by
  unfold emb
  rw [Matrix.mul_assoc, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, h1, Matrix.mul_one,
    add_sub_cancel]

theorem emb_injective (h1 : π * ι = 1) : Function.Injective (emb ι π) := by
  intro R R' h
  unfold emb at h
  have h' : ι * (R - 1) * π = ι * (R' - 1) * π := add_left_cancel h
  have h2 : R - 1 = R' - 1 := by
    calc R - 1 = (π * ι) * (R - 1) * (π * ι) := by rw [h1, Matrix.one_mul, Matrix.mul_one]
      _ = π * (ι * (R - 1) * π) * ι := by simp only [Matrix.mul_assoc]
      _ = π * (ι * (R' - 1) * π) * ι := by rw [h']
      _ = (π * ι) * (R' - 1) * (π * ι) := by simp only [Matrix.mul_assoc]
      _ = R' - 1 := by rw [h1, Matrix.one_mul, Matrix.mul_one]
  exact sub_left_injective h2

theorem emb_isometry {Δ : Matrix (Fin 2) (Fin 2) K} (hMt : Mᵀ = M) (hΔ : Δᵀ = Δ) (h1 : π * ι = 1)
    (h2 : M * ι = πᵀ * Δ) {R : Matrix (Fin 2) (Fin 2) K} (hR : Rᵀ * Δ * R = Δ) :
    (emb ι π R)ᵀ * M * emb ι π R = M := by
  have h2' : ιᵀ * M = Δ * π := by
    have := congrArg Matrix.transpose h2
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hMt, hΔ] at this
  have hX : ∀ X : Matrix (Fin 2) (Fin 3) K, π * (ι * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have r2 : ∀ X : Matrix (Fin 2) (Fin 3) K, M * (ι * X) = πᵀ * (Δ * X) := fun X => by
    rw [← Matrix.mul_assoc, h2, Matrix.mul_assoc]
  have r4 : ∀ X : Matrix (Fin 2) (Fin 3) K, ιᵀ * (M * (ι * X)) = Δ * X := fun X => by
    rw [← Matrix.mul_assoc, h2', Matrix.mul_assoc, hX]
  unfold emb
  have e : (1 + ι * (R - 1) * π)ᵀ * M * (1 + ι * (R - 1) * π) =
      M + M * (ι * ((R - 1) * π)) + πᵀ * ((R - 1)ᵀ * (ιᵀ * M)) +
        πᵀ * ((R - 1)ᵀ * (ιᵀ * (M * (ι * ((R - 1) * π))))) := by
    simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul, Matrix.mul_add,
      Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    abel
  rw [e, r4, r2, h2']
  have e2 : Δ * (R - 1) + (R - 1)ᵀ * Δ + (R - 1)ᵀ * Δ * (R - 1) = 0 := by
    have : Δ * (R - 1) + (R - 1)ᵀ * Δ + (R - 1)ᵀ * Δ * (R - 1) = Rᵀ * Δ * R - Δ := by
      simp only [Matrix.transpose_sub, Matrix.transpose_one]
      noncomm_ring
    rw [this, hR, sub_self]
  have e3 : πᵀ * (Δ * ((R - 1) * π)) + πᵀ * ((R - 1)ᵀ * (Δ * π)) +
      πᵀ * ((R - 1)ᵀ * (Δ * ((R - 1) * π))) =
      πᵀ * ((Δ * (R - 1) + (R - 1)ᵀ * Δ + (R - 1)ᵀ * Δ * (R - 1)) * π) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  rw [add_assoc, add_assoc, ← add_assoc (πᵀ * (Δ * ((R - 1) * π))), e3, e2]
  simp

theorem conj_emb {T : Matrix (Fin 3) (Fin 3) K} {D : Matrix (Fin 2) (Fin 2) K}
    (hT : T * ι = ι * D) (hT' : π * T = D * π) (hDD : D * D = 1) (hTT : T * T = 1)
    (R : Matrix (Fin 2) (Fin 2) K) : T * emb ι π R * T = emb ι π (D * R * D) := by
  unfold emb
  have e : T * (1 + ι * (R - 1) * π) * T = T * T + (T * ι) * (R - 1) * (π * T) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [e, hTT, hT, hT']
  have e2 : D * R * D - 1 = D * (R - 1) * D := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hDD]
  rw [e2]
  simp only [Matrix.mul_assoc]

end Abstract

section Data

variable {K : Type*} [Field K]

@[expose] def planeι (r f : Fin 3 → K) : Matrix (Fin 3) (Fin 2) K :=
  Matrix.of fun i => ![r i, f i]

@[expose] def planeπ (M : Matrix (Fin 3) (Fin 3) K) (r f : Fin 3 → K) (a b : K) :
    Matrix (Fin 2) (Fin 3) K :=
  Matrix.of ![a⁻¹ • (M *ᵥ r), b⁻¹ • (M *ᵥ f)]

theorem dot_mulVec_symm {M : Matrix (Fin 3) (Fin 3) K} (hMt : Mᵀ = M) (x y : Fin 3 → K) :
    (M *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (M *ᵥ y) := by
  rw [Matrix.dotProduct_mulVec]
  have := Matrix.vecMul_transpose M x
  rw [hMt] at this
  rw [this]

theorem planeπ_mul_planeι {M : Matrix (Fin 3) (Fin 3) K} (hMt : Mᵀ = M) {r f : Fin 3 → K}
    {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) (hrr : r ⬝ᵥ (M *ᵥ r) = a) (hff : f ⬝ᵥ (M *ᵥ f) = b)
    (hrf : r ⬝ᵥ (M *ᵥ f) = 0) : planeπ M r f a b * planeι r f = 1 := by
  have d00 : (M *ᵥ r) ⬝ᵥ r = a := by rw [dot_mulVec_symm hMt]; exact hrr
  have d01 : (M *ᵥ r) ⬝ᵥ f = 0 := by rw [dot_mulVec_symm hMt]; exact hrf
  have d10 : (M *ᵥ f) ⬝ᵥ r = 0 := by rw [dotProduct_comm]; exact hrf
  have d11 : (M *ᵥ f) ⬝ᵥ f = b := by rw [dot_mulVec_symm hMt]; exact hff
  ext j k
  fin_cases j <;> fin_cases k
  · show (a⁻¹ • (M *ᵥ r)) ⬝ᵥ r = 1
    rw [smul_dotProduct, d00, smul_eq_mul, inv_mul_cancel₀ ha]
  · show (a⁻¹ • (M *ᵥ r)) ⬝ᵥ f = 0
    rw [smul_dotProduct, d01, smul_zero]
  · show (b⁻¹ • (M *ᵥ f)) ⬝ᵥ r = 0
    rw [smul_dotProduct, d10, smul_zero]
  · show (b⁻¹ • (M *ᵥ f)) ⬝ᵥ f = 1
    rw [smul_dotProduct, d11, smul_eq_mul, inv_mul_cancel₀ hb]

theorem mul_planeι {M : Matrix (Fin 3) (Fin 3) K} {r f : Fin 3 → K} {a b : K} (ha : a ≠ 0)
    (hb : b ≠ 0) :
    M * planeι r f = (planeπ M r f a b)ᵀ * Matrix.diagonal ![a, b] := by
  ext i k
  rw [Matrix.mul_diagonal, Matrix.transpose_apply]
  fin_cases k
  · show (M *ᵥ r) i = (a⁻¹ • (M *ᵥ r)) i * a
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  · show (M *ᵥ f) i = (b⁻¹ • (M *ᵥ f)) i * b
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp

@[expose] def dmat2 (K : Type*) [Field K] : Matrix (Fin 2) (Fin 2) K := !![-1, 0; 0, 1]

theorem dmat2_mul_self : dmat2 K * dmat2 K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dmat2, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_planeι_T {T : Matrix (Fin 3) (Fin 3) K} {r f : Fin 3 → K} (hr : T *ᵥ r = -r)
    (hf : T *ᵥ f = f) : T * planeι r f = planeι r f * dmat2 K := by
  ext i k
  fin_cases k
  · have h := congrFun hr i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.neg_apply] at h
    simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, planeι, dmat2]
    linear_combination h
  · have h := congrFun hf i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h
    simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, planeι, dmat2]
    linear_combination h

theorem planeπ_mul_T {M T : Matrix (Fin 3) (Fin 3) K} {r f : Fin 3 → K} {a b : K}
    (hTM : Tᵀ * M = M * T) (hr : T *ᵥ r = -r) (hf : T *ᵥ f = f) :
    planeπ M r f a b * T = dmat2 K * planeπ M r f a b := by
  have h1 : (M *ᵥ r) ᵥ* T = -(M *ᵥ r) := by
    rw [← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hTM, ← Matrix.mulVec_mulVec, hr,
      Matrix.mulVec_neg]
  have h2 : (M *ᵥ f) ᵥ* T = M *ᵥ f := by
    rw [← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hTM, ← Matrix.mulVec_mulVec, hf]
  ext j k
  fin_cases j
  · show ((a⁻¹ • (M *ᵥ r)) ᵥ* T) k = (dmat2 K * planeπ M r f a b) 0 k
    rw [Matrix.smul_vecMul, h1]
    simp [Matrix.mul_apply, Fin.sum_univ_two, planeπ, dmat2]
  · show ((b⁻¹ • (M *ᵥ f)) ᵥ* T) k = (dmat2 K * planeπ M r f a b) 1 k
    rw [Matrix.smul_vecMul, h2]
    simp [Matrix.mul_apply, Fin.sum_univ_two, planeπ, dmat2]

end Data

end CFSG.RankThree.PartOne.KF1322
