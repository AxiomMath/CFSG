module

import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryNorm
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Norm

open CFSG.ComponentClassification
open scoped Matrix

variable {K : Type*} [Field K] (σ : K ≃+* K)

@[expose] def coordSigma (n : ℕ) : (Fin n → K) →ₛₗ[(σ : K →+* K)] (Fin n → K) where
  toFun v i := σ (v i)
  map_add' v w := by ext i; simp
  map_smul' c v := by ext i; simp

@[simp] theorem coordSigma_apply (n : ℕ) (v : Fin n → K) (i : Fin n) :
    coordSigma σ n v i = σ (v i) := rfl

private theorem q2cS3c_sigma_sigma (hσ : σ ^ 2 = 1) (x : K) :
    (σ : K →+* K) ((σ : K →+* K) x) = x :=
  CatalogueBUnitaryNorm.involutive σ hσ x

section General

variable {V : Type*} [AddCommGroup V] [Module K V]

private theorem q2cS3c_injective
    (T : V →ₛₗ[(σ : K →+* K)] V) (hT : ∀ U : Submodule K V, (U.map T).map T = U) :
    Function.Injective T := by
  intro x y hxy
  have h0 : T (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hspan : Submodule.span K {x - y} = ⊥ := by
    have hmap : (Submodule.span K {x - y}).map T = ⊥ := by
      rw [Submodule.map_span]
      simp [h0]
    have h2 := hT (Submodule.span K {x - y})
    rw [hmap, Submodule.map_bot] at h2
    exact h2.symm
  have hmem : x - y ∈ Submodule.span K {x - y} := Submodule.mem_span_singleton_self _
  rw [hspan] at hmem
  exact sub_eq_zero.mp ((Submodule.mem_bot K).mp hmem)

theorem exists_sq_eq_smul_of_involutive [Nontrivial V] (hσ : σ ^ 2 = 1)
    (T : V →ₛₗ[(σ : K →+* K)] V) (hT : ∀ U : Submodule K V, (U.map T).map T = U) :
    ∃ μ : K, μ ≠ 0 ∧ ∀ v, T (T v) = μ • v := by
  have hσx : ∀ x : K, (σ : K →+* K) ((σ : K →+* K) x) = x :=
    q2cS3c_sigma_sigma σ hσ
  let S : V →ₗ[K] V :=
    { toFun := fun v => T (T v)
      map_add' := by intro v w; simp [map_add]
      map_smul' := by
        intro a v
        rw [LinearMap.map_smulₛₗ T a v,
          LinearMap.map_smulₛₗ T ((σ : K →+* K) a) (T v), hσx a]
        rfl }
  have heig : ∀ v, S v ∈ Submodule.span K {v} := by
    intro v
    have h1 : T v ∈ (Submodule.span K {v}).map T :=
      Submodule.mem_map_of_mem (Submodule.subset_span (by simp))
    have h2 : T (T v) ∈ ((Submodule.span K {v}).map T).map T :=
      Submodule.mem_map_of_mem h1
    rwa [hT (Submodule.span K {v})] at h2
  have hdep : ∀ v, ¬ LinearIndependent K ![v, S v] := by
    intro v hli
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (heig v)
    have h1 : (-a) • v + (1 : K) • S v = 0 := by
      rw [one_smul, ← ha, neg_smul, neg_add_cancel]
    exact one_ne_zero ((LinearIndependent.pair_iff.mp hli) (-a) 1 h1).2
  obtain ⟨μ, hμ⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent (f := S) hdep
  have hSμ : ∀ v, T (T v) = μ • v := by
    intro v
    have h := congrArg (fun f : V →ₗ[K] V => f v) hμ
    simpa [S] using h
  refine ⟨μ, ?_, hSμ⟩
  rintro rfl
  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := exists_ne 0
  have hinj := q2cS3c_injective σ T hT
  have h0 : T (T v) = 0 := by rw [hSμ v, zero_smul]
  have h1 : T v = 0 := hinj (by simpa using h0)
  exact hv (hinj (by simpa using h1))

theorem exists_involutive_smul [Finite K] [Nontrivial V] (hσ : σ ^ 2 = 1) (hne : σ ≠ 1)
    (T : V →ₛₗ[(σ : K →+* K)] V) (hT : ∀ U : Submodule K V, (U.map T).map T = U) :
    ∃ c : K, c ≠ 0 ∧ ∀ v, c • T (c • T v) = v := by
  obtain ⟨μ, hμ0, hμ⟩ := exists_sq_eq_smul_of_involutive σ hσ T hT
  have hσμ : σ μ = μ := by
    obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := exists_ne 0
    have hinj := q2cS3c_injective σ T hT
    have hTv : T v ≠ 0 := fun h => hv (hinj (by simpa using h))
    have h1 : T (T (T v)) = μ • T v := hμ (T v)
    have h2 : T (T (T v)) = σ μ • T v := by
      rw [hμ v, LinearMap.map_smulₛₗ]
      rfl
    rw [h1] at h2
    have h3 : (μ - σ μ) • T v = 0 := by rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact (sub_eq_zero.mp h4).symm
    · exact absurd h4 hTv
  obtain ⟨c, hc⟩ :=
    CatalogueBUnitaryNorm.exists_norm σ hσ hne μ⁻¹ (by rw [map_inv₀, hσμ])
      (inv_ne_zero hμ0)
  refine ⟨c, ?_, ?_⟩
  · intro hc0
    rw [hc0, map_zero, zero_mul] at hc
    exact (inv_ne_zero hμ0) hc.symm
  · intro v
    calc c • T (c • T v) = c • (σ c • T (T v)) := by
          rw [LinearMap.map_smulₛₗ]
          rfl
      _ = (c * σ c) • T (T v) := by rw [smul_smul]
      _ = (c * σ c) • (μ • v) := by rw [hμ v]
      _ = ((c * σ c) * μ) • v := by rw [smul_smul]
      _ = v := by rw [mul_comm c (σ c), hc, inv_mul_cancel₀ hμ0, one_smul]

end General

theorem exists_coord_equiv [Finite K] (hσ : σ ^ 2 = 1) (hne : σ ≠ 1) {n : ℕ} (hn : 0 < n)
    (T : (Fin n → K) →ₛₗ[(σ : K →+* K)] (Fin n → K))
    (hT : ∀ U : Submodule K (Fin n → K), (U.map T).map T = U) :
    ∃ (e : (Fin n → K) ≃ₗ[K] (Fin n → K)) (c : K), c ≠ 0 ∧
      ∀ v, e (c • T v) = coordSigma σ n (e v) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨c, hc0, hc⟩ := exists_involutive_smul σ hσ hne T hT
  obtain ⟨x₀, hx₀⟩ := CatalogueBUnitaryNorm.exists_not_fixed σ hne
  let T' : (Fin n → K) →ₛₗ[(σ : K →+* K)] (Fin n → K) :=
    { toFun := fun v => c • T v
      map_add' := by intro v w; rw [map_add, smul_add]
      map_smul' := by
        intro a v
        rw [LinearMap.map_smulₛₗ, smul_smul, smul_smul, mul_comm c ((σ : K →+* K) a)] }
  have hTT' : ∀ v, T' (T' v) = v := fun v => hc v
  obtain ⟨H, hH⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_fixed_basis_of_ne hx₀ T'
      T'.map_add T'.map_smulₛₗ hTT'
  have hcol : ∀ c : Fin n, T' ((H : Matrix (Fin n) (Fin n) K).col c) =
      (H : Matrix (Fin n) (Fin n) K).col c := by
    intro c
    exact hH c
  have hsum : ∀ u : Fin n → K,
      (∑ c, u c • (H : Matrix (Fin n) (Fin n) K).col c) =
        (H : Matrix (Fin n) (Fin n) K) *ᵥ u := by
    intro u
    ext r
    rw [Matrix.mulVec_apply_eq_sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  have hkey : ∀ u : Fin n → K, T' ((H : Matrix (Fin n) (Fin n) K) *ᵥ u) =
      (H : Matrix (Fin n) (Fin n) K) *ᵥ (fun c => (σ : K →+* K) (u c)) := by
    intro u
    rw [← hsum u, map_sum]
    simp only [LinearMap.map_smulₛₗ, hcol]
    rw [hsum (fun c => (σ : K →+* K) (u c))]
  let e : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    (Matrix.GeneralLinearGroup.toLin (H⁻¹)).toLinearEquiv
  let Hi : Matrix (Fin n) (Fin n) K := ((H⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hHi : (H : Matrix (Fin n) (Fin n) K) * Hi = 1 := by
    change (H : Matrix (Fin n) (Fin n) K) *
      (((H⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) = 1
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel H,
      Matrix.GeneralLinearGroup.coe_one]
  refine ⟨e, c, hc0, fun v => ?_⟩
  have hmain : T' v = (H : Matrix (Fin n) (Fin n) K) *ᵥ
      (fun c => (σ : K →+* K) ((Hi *ᵥ v) c)) := by
    have h1 := hkey (Hi *ᵥ v)
    rw [Matrix.mulVec_mulVec, hHi, Matrix.one_mulVec] at h1
    exact h1
  change (Matrix.GeneralLinearGroup.toLin (H⁻¹) : (Fin n → K) →ₗ[K] (Fin n → K)) (T' v) =
    coordSigma σ n ((Matrix.GeneralLinearGroup.toLin (H⁻¹) : (Fin n → K) →ₗ[K] (Fin n → K)) v)
  rw [hmain]
  simp only [Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel H,
    Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  rfl

theorem exists_coord_equiv_map [Finite K] (hσ : σ ^ 2 = 1) (hne : σ ≠ 1) {n : ℕ} (hn : 0 < n)
    (T : (Fin n → K) →ₛₗ[(σ : K →+* K)] (Fin n → K))
    (hT : ∀ U : Submodule K (Fin n → K), (U.map T).map T = U) :
    ∃ e : (Fin n → K) ≃ₗ[K] (Fin n → K), ∀ U : Submodule K (Fin n → K),
      (U.map T).map e.toLinearMap = (U.map e.toLinearMap).map (coordSigma σ n) := by
  obtain ⟨e, c, hc0, hce⟩ := exists_coord_equiv σ hσ hne hn T hT
  refine ⟨e, fun U => le_antisymm ?_ ?_⟩
  · rintro x ⟨y, ⟨u, hu, rfl⟩, rfl⟩
    have h1 : e (T u) = c⁻¹ • coordSigma σ n (e u) := by
      have h := hce u
      rw [map_smul] at h
      rw [← h, inv_smul_smul₀ hc0]
    show e (T u) ∈ Submodule.map (coordSigma σ n) (Submodule.map e.toLinearMap U)
    rw [h1]
    exact Submodule.smul_mem _ _
      (Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hu))
  · rintro x ⟨y, ⟨u, hu, rfl⟩, rfl⟩
    have h2 : coordSigma σ n (e u) = e (T ((σ : K →+* K) c • u)) := by
      rw [LinearMap.map_smulₛₗ, q2cS3c_sigma_sigma σ hσ c]
      exact (hce u).symm
    show coordSigma σ n (e u) ∈ Submodule.map e.toLinearMap (Submodule.map T U)
    rw [h2]
    exact Submodule.mem_map_of_mem
      (Submodule.mem_map_of_mem (Submodule.smul_mem U ((σ : K →+* K) c) hu))

end CFSG.ClassicalInvolution.Phan.PhanE.Norm
