module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotAutUBasic
public import CFSG.CGT.Timmesfeld75.ListWCLinBasic

public noncomputable section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix
open CFSG.ComponentClassification
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.CGT.Timmesfeld75

variable {K : Type*} [Field K]

theorem map_tvSL (σ : K ≃+* K) {n : ℕ} {a f : Fin n → K} (hf : f ⬝ᵥ a = 0) :
    ((SpecialLinearGroup.map σ.toRingHom (tvSL a f hf) :
        SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 + vecMulVec (fun i => σ (a i)) (fun i => σ (f i)) := by
  ext i j
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    CFSG.CGT.Timmesfeld75.coe_tvSL]
  by_cases hij : i = j
  · subst hij
    simp [Matrix.vecMulVec_apply]
  · simp [Matrix.vecMulVec_apply, hij]

theorem fieldAut_eq_one_of_conjAut_mul_fixes_tvCenter [Finite K] {n : ℕ} (hn : 3 ≤ n)
    {a : Fin n → K} (ha : a ≠ 0) (A : GL (Fin n) K) (σ : K ≃+* K)
    (hfix : ∀ (f : Fin n → K) (hf : f ⬝ᵥ a = 0),
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n K A *
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut n K σ)
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj n K
          (CFSG.CGT.Timmesfeld75.tvSL a f hf)) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj n K
        (CFSG.CGT.Timmesfeld75.tvSL a f hf)) :
    σ = 1 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : Fin n, a i ≠ 0 := Function.ne_iff.mp ha
  have hcard : 1 < (Finset.univ.erase i).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨j₀, hj₀, k, hk, hjk⟩ := Finset.one_lt_card.mp hcard
  have hj₀i : j₀ ≠ i := (Finset.mem_erase.mp hj₀).1
  have hki : k ≠ i := (Finset.mem_erase.mp hk).1
  have hkj₀ : k ≠ j₀ := fun h => hjk h.symm
  let f : Fin n → K := Pi.single i (a j₀) - Pi.single j₀ (a i)
  have hf : f ⬝ᵥ a = 0 := by
    simp only [f, sub_dotProduct, single_dotProduct]
    ring
  have hfk : f k = 0 := by
    simp [f, hki, hkj₀]
  have hfne : f ≠ 0 := by
    intro h0
    have hfj : f j₀ = -a i := by simp [f, hj₀i]
    have := congrFun h0 j₀
    rw [hfj] at this
    exact hi (neg_eq_zero.mp this)
  let μ : K :=
    (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (fun t => σ (a t))) i / a i
  have key : ∀ (c : K) (m : Fin n),
      c * (f ᵥ* ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) m =
        μ * (σ c * σ (f m)) := by
    intro c m
    have hfc : (c • f) ⬝ᵥ a = 0 := by
      rw [smul_dotProduct, hf, smul_zero]
    have hN : vecMulVec a (c • f) * vecMulVec a (c • f) = 0 := by
      rw [Matrix.vecMulVec_mul_vecMulVec, hfc, zero_smul, Matrix.vecMulVec_zero]
    have hM : vecMulVec (fun t => σ (a t)) (fun t => σ ((c • f) t)) *
        vecMulVec (fun t => σ (a t)) (fun t => σ ((c • f) t)) = 0 := by
      rw [Matrix.vecMulVec_mul_vecMulVec]
      have hdot : (fun t => σ ((c • f) t)) ⬝ᵥ (fun t => σ (a t)) = 0 := by
        have h := congrArg σ.toRingHom hfc
        rw [RingHom.map_dotProduct] at h
        change (σ.toRingHom ∘ (c • f)) ⬝ᵥ (σ.toRingHom ∘ a) = 0
        simpa only [map_zero] using h
      rw [hdot, zero_smul, Matrix.vecMulVec_zero]
    have hproj : proj n K (CatalogueBHigherLinearAction.slConjugation n K A
        (SpecialLinearGroup.map σ.toRingHom (tvSL a (c • f) hfc))) =
        proj n K (tvSL a (c • f) hfc) := by
      simpa only [MulAut.mul_apply, conjAut_proj, fieldAut_proj] using hfix (c • f) hfc
    have hNA : vecMulVec a (c • f) * ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          vecMulVec (fun t => σ (a t)) (fun t => σ ((c • f) t)) := by
      refine CFSG.SeitzReduction.LinearPilot.mul_eq_of_proj_eq A
        (x := CatalogueBHigherLinearAction.slConjugation n K A
          (SpecialLinearGroup.map σ.toRingHom (tvSL a (c • f) hfc)))
        (u := tvSL a (c • f) hfc)
        (M := vecMulVec (fun t => σ (a t)) (fun t => σ ((c • f) t)))
        (N := vecMulVec a (c • f)) ?_ ?_ hM hN (k := k) ?_ hproj
      · rw [LinearFlag.coe_slConjugation, map_tvSL]
      · rw [CFSG.CGT.Timmesfeld75.coe_tvSL]
      · rw [Matrix.vecMulVec_apply]
        calc a k * (c • f) k = c * (a k * f k) := by
              rw [Pi.smul_apply, smul_eq_mul]; ring
          _ = 0 := by rw [hfk]; simp
    have hvec : ((c • f) ᵥ* ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) m =
        μ * σ ((c • f) m) := by
      have hij := congrFun (congrFun hNA i) m
      rw [Matrix.vecMulVec_mul, Matrix.mul_vecMulVec] at hij
      simp only [Matrix.vecMulVec_apply] at hij
      calc ((c • f) ᵥ* ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) m
          = (a i)⁻¹ * (a i * ((c • f) ᵥ* ((A : GL (Fin n) K) :
              Matrix (Fin n) (Fin n) K)) m) := by
              rw [← mul_assoc, inv_mul_cancel₀ hi, one_mul]
        _ = (a i)⁻¹ * (((((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
              (fun t => σ (a t))) i) * σ ((c • f) m)) := by rw [hij]
        _ = μ * σ ((c • f) m) := by
              simp only [μ, div_eq_inv_mul]
              ring
    calc c * (f ᵥ* ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) m
        = ((c • f) ᵥ* ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) m := by
            rw [Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul]
      _ = μ * σ ((c • f) m) := hvec
      _ = μ * (σ c * σ (f m)) := by
            rw [Pi.smul_apply, smul_eq_mul, map_mul]
  have hfA : f ᵥ* ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ 0 := by
    intro h0
    apply hfne
    have hAA : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← GeneralLinearGroup.coe_mul, mul_inv_cancel, GeneralLinearGroup.coe_one]
    have h := congrArg (fun v => v ᵥ* ((A⁻¹ : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) h0
    simpa [Matrix.vecMul_vecMul, hAA] using h
  obtain ⟨m, hm⟩ : ∃ m : Fin n,
      (f ᵥ* ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) m ≠ 0 :=
    Function.ne_iff.mp hfA
  have h1 : (f ᵥ* ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) m = μ * σ (f m) := by
    simpa using key 1 m
  refine RingEquiv.ext fun c => ?_
  show σ c = c
  have hc := key c m
  rw [h1] at hc
  have hcommon : c * (μ * σ (f m)) = σ c * (μ * σ (f m)) := by
    rw [hc]; ring
  exact (mul_right_cancel₀ (by rwa [← h1]) hcommon).symm

end CFSG.LocalAnalysis.WeakClosure81
