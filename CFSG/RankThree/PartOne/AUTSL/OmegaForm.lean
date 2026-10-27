module

public import CFSG.RankThree.PartOne.AUTSL.GramRel
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

public section

namespace CFSG.RankThree.PartOne.AUTSL

open Matrix

section Form

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_polar_matrix (Q : QuadraticForm K (ι → K))
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) :
    ∃ J : Matrix ι ι K, (∀ v w, QuadraticMap.polar Q v w = v ⬝ᵥ J *ᵥ w) ∧ Jᵀ = J ∧ IsUnit J := by
  set J : Matrix ι ι K := LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q) with hJ
  have hpol : ∀ v w, QuadraticMap.polar Q v w = v ⬝ᵥ J *ᵥ w := by
    intro v w
    rw [← Matrix.toBilin'_apply', hJ, Matrix.toBilin'_toMatrix',
      QuadraticMap.polarBilin_apply_apply]
  refine ⟨J, hpol, ?_, ?_⟩
  · ext i j
    simp only [Matrix.transpose_apply, hJ, LinearMap.BilinForm.toMatrix'_apply,
      QuadraticMap.polarBilin_apply_apply]
    exact QuadraticMap.polar_comm _ _ _
  · have h1 : J.Nondegenerate := LinearMap.BilinForm.nondegenerate_toMatrix'_iff.2 hnd
    have h2 : J.det ≠ 0 := Matrix.nondegenerate_iff_det_ne_zero.1 h1
    exact (Matrix.isUnit_iff_isUnit_det J).2 (isUnit_iff_ne_zero.2 h2)

theorem gram_of_isometry (Q : QuadraticForm K (ι → K)) (J : Matrix ι ι K)
    (hpol : ∀ v w, QuadraticMap.polar Q v w = v ⬝ᵥ J *ᵥ w) (g : Matrix ι ι K)
    (hg : ∀ v, Q (g *ᵥ v) = Q v) : gᵀ * J * g = J := by
  have hinv : ∀ x y, QuadraticMap.polar Q (g *ᵥ x) (g *ᵥ y) = QuadraticMap.polar Q x y := by
    intro x y
    simp only [QuadraticMap.polar]
    rw [← Matrix.mulVec_add, hg, hg, hg]
  have hentry : ∀ M : Matrix ι ι K, ∀ i j,
      M i j = Pi.single i (1 : K) ⬝ᵥ M *ᵥ Pi.single j (1 : K) := by
    intro M i j
    rw [Matrix.mulVec_single_one, single_dotProduct, one_mul]
    rfl
  ext i j
  have h1 : (gᵀ * J * g) i j =
      (g *ᵥ Pi.single i (1 : K)) ⬝ᵥ J *ᵥ (g *ᵥ Pi.single j (1 : K)) := by
    rw [hentry (gᵀ * J * g) i j, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      dotProduct_mulVec (Pi.single i (1 : K)) gᵀ, Matrix.vecMul_transpose]
  rw [h1, ← hpol, hinv, hpol, ← hentry J i j]

omit [DecidableEq ι] in
theorem dot_conj {R : Type*} [CommRing R] (Pi J : Matrix ι ι R) (x y : ι → R) :
    (Pi *ᵥ x) ⬝ᵥ J *ᵥ (Pi *ᵥ y) = x ⬝ᵥ (Piᵀ * J * Pi) *ᵥ y := by
  have h1 : (Piᵀ * J * Pi) *ᵥ y = Piᵀ *ᵥ (J *ᵥ (Pi *ᵥ y)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [h1, dotProduct_mulVec x Piᵀ, Matrix.vecMul_transpose]

theorem polar_coord {K' : Type*} [Field K'] [Algebra K K'] (J : Matrix ι ι K) (P : GL ι K')
    (v w : ι → K) :
    algebraMap K K' (v ⬝ᵥ J *ᵥ w) = ((P : Matrix ι ι K') *ᵥ (algebraMap K K' ∘ v)) ⬝ᵥ
      ((((P⁻¹ : GL ι K') : Matrix ι ι K')ᵀ * J.map (algebraMap K K') *
        ((P⁻¹ : GL ι K') : Matrix ι ι K')) *ᵥ ((P : Matrix ι ι K') *ᵥ (algebraMap K K' ∘ w))) := by
  have hPiP : ((P⁻¹ : GL ι K') : Matrix ι ι K') * (P : Matrix ι ι K') = 1 := Units.inv_mul P
  have h1 : algebraMap K K' (v ⬝ᵥ J *ᵥ w) =
      (algebraMap K K' ∘ v) ⬝ᵥ (J.map (algebraMap K K') *ᵥ (algebraMap K K' ∘ w)) := by
    rw [RingHom.map_dotProduct]
    congr 1
    funext i
    exact RingHom.map_mulVec (algebraMap K K') J w i
  have h2 : ∀ z : ι → K', z = ((P⁻¹ : GL ι K') : Matrix ι ι K') *ᵥ ((P : Matrix ι ι K') *ᵥ z) := by
    intro z
    rw [Matrix.mulVec_mulVec, hPiP, Matrix.one_mulVec]
  rw [h1, ← dot_conj]
  conv_lhs => rw [h2 (algebraMap K K' ∘ v), h2 (algebraMap K K' ∘ w)]

end Form

end CFSG.RankThree.PartOne.AUTSL
