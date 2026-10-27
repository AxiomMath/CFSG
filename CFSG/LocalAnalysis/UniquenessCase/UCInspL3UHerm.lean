module

public import CFSG.LocalAnalysis.UniquenessCase.UCInspL3UE
public import Mathlib.FieldTheory.Finite.Trace

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Insp

open Matrix CFSG.LieType.Universal.Unitary

section MatrixLemmas

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem conjTr_mul_eq_of_forall {n : ℕ} (S M : Matrix (Fin n) (Fin n) K)
    (h : ∀ u v : Fin n → K, (σ ∘ (M *ᵥ u)) ⬝ᵥ (S *ᵥ (M *ᵥ v)) = (σ ∘ u) ⬝ᵥ (S *ᵥ v)) :
    conjTr σ M * S * M = S := by
  ext i j
  have h1 := h (Pi.single i 1) (Pi.single j 1)
  have e : (σ ∘ (Pi.single i 1 : Fin n → K)) = Pi.single i 1 := by
    ext k
    by_cases hk : k = i <;> simp [Pi.single_apply, hk]
  have hL : (σ ∘ (M *ᵥ (Pi.single i 1 : Fin n → K))) ⬝ᵥ
      (S *ᵥ (M *ᵥ (Pi.single j 1 : Fin n → K))) = (conjTr σ M * S * M) i j := by
    rw [Matrix.mulVec_single_one M i, Matrix.mulVec_single_one M j, Matrix.mul_assoc,
      Matrix.mul_apply]
    simp [dotProduct, Matrix.mulVec, conjTr, Matrix.mul_apply, Matrix.col]
  rw [hL, e, single_dotProduct, one_mul, Matrix.mulVec_single_one] at h1
  exact h1

theorem det_eq_one_of_isometry {n : ℕ} {S M : Matrix (Fin n) (Fin n) K} (hS : S.det ≠ 0)
    (hM : conjTr σ M * S * M = S) {m Q : ℕ} (hσQ : ∀ c : K, σ c = c ^ Q)
    (h1 : M.det ^ m = 1) (hcop : Nat.Coprime m (Q + 1)) : M.det = 1 := by
  have h2 := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_mul, det_conjTr] at h2
  have h3 : σ M.det * M.det = 1 := by
    have h4 : (σ M.det * M.det) * S.det = 1 * S.det := by
      rw [one_mul]
      calc (σ M.det * M.det) * S.det = σ M.det * S.det * M.det := by ring
        _ = S.det := h2
    exact mul_right_cancel₀ hS h4
  have h5 : M.det ^ (Q + 1) = 1 := by
    rw [pow_succ, ← hσQ]
    exact h3
  exact (pow_eq_one_iff_of_coprime hcop).1 ⟨h1, h5⟩

end MatrixLemmas

section Herm

variable {K L : Type} [Field K] [Field L] [Algebra K L] [Finite L]
variable (σ : K ≃+* K) (β : L ≃+* L)

@[expose] noncomputable def hermForm
    (hβK : ∀ c : K, β (algebraMap K L c) = algebraMap K L (σ c)) :
    L →ₛₗ[(σ : K →+* K)] L →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (σ : K →+* K) (RingHom.id K) (fun x y => Algebra.trace K L (β x * y))
    (fun x x' y => by rw [map_add, add_mul, map_add])
    (fun c x y => by
      have hc : β (c • x) = σ c • β x := by
        rw [Algebra.smul_def, map_mul, hβK, Algebra.smul_def]
      rw [hc, smul_mul_assoc, map_smul]
      rfl)
    (fun x y y' => by rw [mul_add, map_add])
    (fun c x y => by
      rw [mul_smul_comm, map_smul]
      rfl)

variable (hβK : ∀ c : K, β (algebraMap K L c) = algebraMap K L (σ c))

include hβK

theorem hermForm_apply (x y : L) :
    hermForm σ β hβK x y = Algebra.trace K L (β x * y) := rfl

theorem trace_beta (z : L) : Algebra.trace K L (β z) = σ (Algebra.trace K L z) := by
  apply (algebraMap K L).injective
  rw [← hβK, FiniteField.algebraMap_trace_eq_sum_pow K L (β z),
    FiniteField.algebraMap_trace_eq_sum_pow K L z, map_sum]
  simp only [map_pow]

variable {β}

theorem hermForm_symm (hββ : ∀ x : L, β (β x) = x) (x y : L) :
    σ (hermForm σ β hβK x y) = hermForm σ β hβK y x := by
  simp only [hermForm_apply]
  rw [← trace_beta σ β hβK, map_mul, hββ, mul_comm]

theorem hermForm_nondeg [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hββ : ∀ x : L, β (β x) = x) {y : L} (hy : ∀ x, hermForm σ β hβK x y = 0) : y = 0 := by
  refine (traceForm_nondegenerate K L).1 y (fun z => ?_)
  rw [Algebra.traceForm_apply, mul_comm]
  have := hy (β z)
  rwa [hermForm_apply, hββ] at this

variable (b : Module.Basis (Fin 3) K L)

@[expose] noncomputable def gram : Matrix (Fin 3) (Fin 3) K :=
  LinearMap.toMatrix₂ b b (hermForm σ β hβK)

theorem gram_apply (i j : Fin 3) : gram σ hβK b i j = hermForm σ β hβK (b i) (b j) := by
  simp [gram]

theorem conjTr_gram (hββ : ∀ x : L, β (β x) = x) :
    conjTr σ (gram σ hβK b) = gram σ hβK b := by
  ext i j
  show σ (gram σ hβK b j i) = gram σ hβK b i j
  rw [gram_apply, gram_apply, hermForm_symm σ hβK hββ]

omit hβK in
theorem repr_equivFun_symm (u : Fin 3 → K) : ⇑(b.repr (b.equivFun.symm u)) = u := by
  rw [← Module.Basis.equivFun_apply]
  exact b.equivFun.apply_symm_apply u

theorem det_gram_ne_zero [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hββ : ∀ x : L, β (β x) = x) : (gram σ hβK b).det ≠ 0 := by
  intro h0
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hry : ⇑(b.repr (b.equivFun.symm c)) = c := repr_equivFun_symm b c
  have hy : b.equivFun.symm c ≠ 0 := by
    intro hy0
    apply hc0
    rw [← hry, hy0]
    ext i
    simp
  apply hy
  apply hermForm_nondeg σ hβK hββ
  intro x
  rw [apply_eq_dotProduct_toMatrix₂_mulVec b b (hermForm σ β hβK) x (b.equivFun.symm c), hry]
  have hc' : (LinearMap.toMatrix₂ b b (hermForm σ β hβK)) *ᵥ (⇑(RingHom.id K) ∘ c) = 0 := hc
  rw [hc', dotProduct_zero]

theorem conjTr_mul_gram_mul (T : L →ₗ[K] L)
    (hT : ∀ x y, hermForm σ β hβK (T x) (T y) = hermForm σ β hβK x y) :
    conjTr σ (LinearMap.toMatrix b b T) * gram σ hβK b * LinearMap.toMatrix b b T =
      gram σ hβK b := by
  apply conjTr_mul_eq_of_forall
  intro u v
  have hu := LinearMap.toMatrix_mulVec_repr b b T (b.equivFun.symm u)
  have hv := LinearMap.toMatrix_mulVec_repr b b T (b.equivFun.symm v)
  have hru : ⇑(b.repr (b.equivFun.symm u)) = u := repr_equivFun_symm b u
  have hrv : ⇑(b.repr (b.equivFun.symm v)) = v := repr_equivFun_symm b v
  have h := hT (b.equivFun.symm u) (b.equivFun.symm v)
  rw [apply_eq_dotProduct_toMatrix₂_mulVec b b (hermForm σ β hβK),
    apply_eq_dotProduct_toMatrix₂_mulVec b b (hermForm σ β hβK) (b.equivFun.symm u),
    ← hu, ← hv, hru, hrv] at h
  exact h

end Herm

end CFSG.LocalAnalysis.UniquenessCase.UCK.Insp
