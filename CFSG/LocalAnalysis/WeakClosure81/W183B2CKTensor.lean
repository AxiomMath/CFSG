module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.Algebra.Central.End

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open scoped TensorProduct

variable {k : Type} [Field k] {U₁ U₂ : Type} [AddCommGroup U₁] [Module k U₁] [AddCommGroup U₂]
  [Module k U₂]

section PureTensor

variable {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

private lemma w183b2_tmul_ne_zero {x : M} {y : N} (hx : x ≠ 0) (hy : y ≠ 0) :
    x ⊗ₜ[k] y ≠ 0 := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hy
  intro h
  have h1 := congrArg (fun t => TensorProduct.rid k M (LinearMap.lTensor M φ t)) h
  simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, hφ, one_smul, map_zero] at h1
  exact hx h1

end PureTensor

private noncomputable def w183b2_lTensorRid {M W : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup W] [Module k W] (φ : Module.Dual k (Module.End k M)) :
    Module.End k W ⊗[k] Module.End k M →ₗ[k] Module.End k W :=
  (TensorProduct.rid k (Module.End k W)).toLinearMap ∘ₗ
    LinearMap.lTensor (Module.End k W) φ

private lemma w183b2_lTensorRid_tmul {M W : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup W] [Module k W] (φ : Module.Dual k (Module.End k M))
    (X : Module.End k W) (Y : Module.End k M) :
    w183b2_lTensorRid φ (X ⊗ₜ[k] Y) = φ Y • X := by
  simp only [w183b2_lTensorRid, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul]

private noncomputable def w183b2_rTensorLid {M W : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup W] [Module k W] (φ : Module.Dual k (Module.End k W)) :
    Module.End k W ⊗[k] Module.End k M →ₗ[k] Module.End k M :=
  (TensorProduct.lid k (Module.End k M)).toLinearMap ∘ₗ
    LinearMap.rTensor (Module.End k M) φ

private lemma w183b2_rTensorLid_tmul {M W : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup W] [Module k W] (φ : Module.Dual k (Module.End k W))
    (X : Module.End k W) (Y : Module.End k M) :
    w183b2_rTensorLid φ (X ⊗ₜ[k] Y) = φ X • Y := by
  simp only [w183b2_rTensorLid, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.rTensor_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul]

theorem w183b2_map_eq_map [FiniteDimensional k U₁] [FiniteDimensional k U₂]
    {a a' : Module.End k U₁} {b b' : Module.End k U₂} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : TensorProduct.map a b = TensorProduct.map a' b') :
    ∃ c : k, c ≠ 0 ∧ a' = c • a ∧ b = c • b' := by
  have ht : a ⊗ₜ[k] b = a' ⊗ₜ[k] b' := by
    apply (homTensorHomEquiv k U₁ U₂ U₁ U₂).injective
    simpa using h
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hb
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_eq_one k ha
  have h1 : a = φ b' • a' := by
    have hc := congrArg (w183b2_lTensorRid (M := U₂) φ) ht
    simpa [w183b2_lTensorRid_tmul, hφ] using hc
  have h2 : b = ψ a' • b' := by
    have hc := congrArg (w183b2_rTensorLid (M := U₂) ψ) ht
    simpa [w183b2_rTensorLid_tmul, hψ] using hc
  have ha' : a' ≠ 0 := by
    intro h0
    rw [h0, smul_zero] at h1
    exact ha h1
  have hb' : b' ≠ 0 := by
    intro h0
    rw [h0, smul_zero] at h2
    exact hb h2
  have hne : a' ⊗ₜ[k] b' ≠ 0 := w183b2_tmul_ne_zero ha' hb'
  have hscal : φ b' * ψ a' = 1 := by
    have h3 : (φ b' * ψ a') • (a' ⊗ₜ[k] b') = (1 : k) • (a' ⊗ₜ[k] b') := by
      rw [one_smul]
      calc (φ b' * ψ a') • (a' ⊗ₜ[k] b')
          = (φ b' • a') ⊗ₜ[k] (ψ a' • b') :=
            (TensorProduct.smul_tmul_smul (φ b') (ψ a') a' b').symm
        _ = a ⊗ₜ[k] b := by rw [← h1, ← h2]
        _ = a' ⊗ₜ[k] b' := ht
    exact (smul_left_inj hne).mp h3
  have hφb' : φ b' ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hscal
    exact one_ne_zero hscal.symm
  refine ⟨(φ b')⁻¹, inv_ne_zero hφb', ?_, ?_⟩
  · rw [h1, smul_smul, inv_mul_cancel₀ hφb', one_smul]
  · rw [h2, eq_inv_of_mul_eq_one_right hscal]

theorem w183b2_map_eq_one [FiniteDimensional k U₁] [FiniteDimensional k U₂] [Nontrivial U₁]
    [Nontrivial U₂] {a : Module.End k U₁} {b : Module.End k U₂}
    (h : TensorProduct.map a b = 1) : ∃ c : k, c ≠ 0 ∧ a = c • 1 ∧ b = c⁻¹ • 1 := by
  haveI : Nontrivial (U₁ ⊗[k] U₂) := by
    obtain ⟨x, hx⟩ := exists_ne (0 : U₁)
    obtain ⟨y, hy⟩ := exists_ne (0 : U₂)
    exact ⟨0, x ⊗ₜ[k] y, (w183b2_tmul_ne_zero hx hy).symm⟩
  have ha : a ≠ 0 := by
    intro h0
    have hzero : TensorProduct.map a b = 0 := by simp [h0]
    rw [hzero] at h
    exact one_ne_zero h.symm
  have hb : b ≠ 0 := by
    intro h0
    have hzero : TensorProduct.map a b = 0 := by simp [h0]
    rw [hzero] at h
    exact one_ne_zero h.symm
  obtain ⟨c, hc0, hc1, hcb⟩ :=
    w183b2_map_eq_map ha hb (by rwa [TensorProduct.map_one])
  refine ⟨c⁻¹, inv_ne_zero hc0, ?_, ?_⟩
  · rw [hc1, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  · rw [hcb, inv_inv]

section InnerConj

variable {W M : Type*} [AddCommGroup W] [Module k W] [AddCommGroup M] [Module k M]

private lemma w183b2_map_injective_left [Nontrivial M] :
    Function.Injective (fun X : Module.End k W =>
      TensorProduct.map X (LinearMap.id : Module.End k M)) := by
  intro X Y h
  by_contra hXY
  have hne : X - Y ≠ 0 := sub_ne_zero.mpr hXY
  obtain ⟨v, hv⟩ : ∃ v, (X - Y) v ≠ 0 := by
    by_contra hcon
    exact hne (LinearMap.ext fun v => not_not.mp (not_exists.mp hcon v))
  obtain ⟨w, hw⟩ := exists_ne (0 : M)
  have h1 : X v ⊗ₜ[k] w = Y v ⊗ₜ[k] w := by
    have := congrArg (fun f : W ⊗[k] M →ₗ[k] W ⊗[k] M => f (v ⊗ₜ[k] w)) h
    simpa using this
  have h2 : ((X - Y) v) ⊗ₜ[k] w = 0 := by
    rw [LinearMap.sub_apply, TensorProduct.sub_tmul, h1, sub_self]
  exact w183b2_tmul_ne_zero hv hw h2

private lemma w183b2_map_injective_right [Nontrivial M] :
    Function.Injective (fun X : Module.End k W =>
      TensorProduct.map (LinearMap.id : Module.End k M) X) := by
  intro X Y h
  by_contra hXY
  have hne : X - Y ≠ 0 := sub_ne_zero.mpr hXY
  obtain ⟨w, hw⟩ : ∃ w, (X - Y) w ≠ 0 := by
    by_contra hcon
    exact hne (LinearMap.ext fun w => not_not.mp (not_exists.mp hcon w))
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  have h1 : v ⊗ₜ[k] X w = v ⊗ₜ[k] Y w := by
    have := congrArg (fun f : M ⊗[k] W →ₗ[k] M ⊗[k] W => f (v ⊗ₜ[k] w)) h
    simpa using this
  have h2 : v ⊗ₜ[k] ((X - Y) w) = 0 := by
    rw [LinearMap.sub_apply, TensorProduct.tmul_sub, h1, sub_self]
  exact w183b2_tmul_ne_zero hv hw h2

private lemma w183b2_map_mul_id (A B : Module.End k W) :
    TensorProduct.map (A * B) (LinearMap.id : Module.End k M) =
      TensorProduct.map A LinearMap.id * TensorProduct.map B LinearMap.id :=
  TensorProduct.map_comp A LinearMap.id B LinearMap.id

private lemma w183b2_map_id_mul (A B : Module.End k W) :
    TensorProduct.map (LinearMap.id : Module.End k M) (A * B) =
      TensorProduct.map (LinearMap.id : Module.End k M) A *
        TensorProduct.map (LinearMap.id : Module.End k M) B :=
  TensorProduct.map_comp LinearMap.id A LinearMap.id B

private noncomputable def w183b2_sigmaL (T : Module.End k (W ⊗[k] M))
    (h : ∀ X : Module.End k W, ∃ X' : Module.End k W,
      T * TensorProduct.map X LinearMap.id = TensorProduct.map X' LinearMap.id * T) :
    Module.End k W → Module.End k W :=
  fun X => (h X).choose

private lemma w183b2_sigmaL_spec (T : Module.End k (W ⊗[k] M))
    (h : ∀ X : Module.End k W, ∃ X' : Module.End k W,
      T * TensorProduct.map X LinearMap.id = TensorProduct.map X' LinearMap.id * T) (X) :
    T * TensorProduct.map X LinearMap.id =
      TensorProduct.map (w183b2_sigmaL T h X) LinearMap.id * T :=
  (h X).choose_spec

private lemma w183b2_sigmaL_congr {T : Module.End k (W ⊗[k] M)} (hT : IsUnit T) [Nontrivial M]
    {A B : Module.End k W}
    (hAB : TensorProduct.map A LinearMap.id * T = TensorProduct.map B LinearMap.id * T) :
    A = B :=
  w183b2_map_injective_left (hT.mul_right_cancel hAB)

private lemma w183b2_sigmaL_zero (T : Module.End k (W ⊗[k] M)) (hT : IsUnit T) [Nontrivial M]
    (h : ∀ X : Module.End k W, ∃ X' : Module.End k W,
      T * TensorProduct.map X LinearMap.id = TensorProduct.map X' LinearMap.id * T) :
    w183b2_sigmaL T h 0 = 0 := by
  apply w183b2_sigmaL_congr hT
  rw [← w183b2_sigmaL_spec T h 0]
  simp

private lemma w183b2_sigmaL_one (T : Module.End k (W ⊗[k] M)) (hT : IsUnit T) [Nontrivial M]
    (h : ∀ X : Module.End k W, ∃ X' : Module.End k W,
      T * TensorProduct.map X LinearMap.id = TensorProduct.map X' LinearMap.id * T) :
    w183b2_sigmaL T h 1 = 1 := by
  have hmap : TensorProduct.map (1 : Module.End k W) (LinearMap.id : Module.End k M) = 1 :=
    TensorProduct.map_id
  apply w183b2_sigmaL_congr hT
  rw [← w183b2_sigmaL_spec T h 1, hmap, mul_one, one_mul]

private lemma w183b2_sigmaL_add (T : Module.End k (W ⊗[k] M)) (hT : IsUnit T) [Nontrivial M]
    (h : ∀ X : Module.End k W, ∃ X' : Module.End k W,
      T * TensorProduct.map X LinearMap.id = TensorProduct.map X' LinearMap.id * T)
    (X Y : Module.End k W) :
    w183b2_sigmaL T h (X + Y) = w183b2_sigmaL T h X + w183b2_sigmaL T h Y := by
  apply w183b2_sigmaL_congr hT
  rw [← w183b2_sigmaL_spec T h (X + Y), TensorProduct.map_add_left, mul_add,
    w183b2_sigmaL_spec T h X, w183b2_sigmaL_spec T h Y, TensorProduct.map_add_left, add_mul]

private lemma w183b2_sigmaL_mul (T : Module.End k (W ⊗[k] M)) (hT : IsUnit T) [Nontrivial M]
    (h : ∀ X : Module.End k W, ∃ X' : Module.End k W,
      T * TensorProduct.map X LinearMap.id = TensorProduct.map X' LinearMap.id * T)
    (X Y : Module.End k W) :
    w183b2_sigmaL T h (X * Y) = w183b2_sigmaL T h X * w183b2_sigmaL T h Y := by
  apply w183b2_sigmaL_congr hT
  rw [← w183b2_sigmaL_spec T h (X * Y), w183b2_map_mul_id X Y]
  rw [w183b2_map_mul_id (w183b2_sigmaL T h X) (w183b2_sigmaL T h Y),
    ← mul_assoc, w183b2_sigmaL_spec T h X, mul_assoc, w183b2_sigmaL_spec T h Y, mul_assoc]

private lemma w183b2_sigmaL_smul (T : Module.End k (W ⊗[k] M)) (hT : IsUnit T) [Nontrivial M]
    (h : ∀ X : Module.End k W, ∃ X' : Module.End k W,
      T * TensorProduct.map X LinearMap.id = TensorProduct.map X' LinearMap.id * T)
    (r : k) (X : Module.End k W) :
    w183b2_sigmaL T h (r • X) = r • w183b2_sigmaL T h X := by
  apply w183b2_sigmaL_congr hT
  rw [← w183b2_sigmaL_spec T h (r • X), TensorProduct.map_smul_left, Algebra.mul_smul_comm,
    w183b2_sigmaL_spec T h X, TensorProduct.map_smul_left, Algebra.smul_mul_assoc]

private lemma w183b2_sigmaL_injective (T : Module.End k (W ⊗[k] M)) (hT : IsUnit T) [Nontrivial M]
    (h : ∀ X : Module.End k W, ∃ X' : Module.End k W,
      T * TensorProduct.map X LinearMap.id = TensorProduct.map X' LinearMap.id * T) :
    Function.Injective (w183b2_sigmaL T h) := by
  intro X Y hXY
  have h1 : T * TensorProduct.map X LinearMap.id = T * TensorProduct.map Y LinearMap.id := by
    rw [w183b2_sigmaL_spec T h X, hXY, ← w183b2_sigmaL_spec T h Y]
  exact w183b2_map_injective_left (hT.mul_left_cancel h1)

private lemma w183b2_exists_conj_of_normalizes [FiniteDimensional k W] [Nontrivial M]
    (T : Module.End k (W ⊗[k] M)) (hT : IsUnit T)
    (h : ∀ X : Module.End k W, ∃ X' : Module.End k W,
      T * TensorProduct.map X LinearMap.id = TensorProduct.map X' LinearMap.id * T) :
    ∃ a : W ≃ₗ[k] W, ∀ (X X' : Module.End k W),
      T * TensorProduct.map X LinearMap.id = TensorProduct.map X' LinearMap.id * T →
      X' = a.conjAlgEquiv k X := by
  let σ := w183b2_sigmaL T h
  let rh : Module.End k W →+* Module.End k W :=
    { toFun := σ
      map_one' := w183b2_sigmaL_one T hT h
      map_mul' := w183b2_sigmaL_mul T hT h
      map_zero' := w183b2_sigmaL_zero T hT h
      map_add' := w183b2_sigmaL_add T hT h }
  let f : Module.End k W →ₐ[k] Module.End k W :=
    AlgHom.mk' rh (fun r X => w183b2_sigmaL_smul T hT h r X)
  have hf_inj : Function.Injective f := w183b2_sigmaL_injective T hT h
  have hf_bij : Function.Bijective f :=
    ⟨hf_inj, LinearMap.surjective_of_injective (f := f.toLinearMap) hf_inj⟩
  let e : Module.End k W ≃ₐ[k] Module.End k W := AlgEquiv.ofBijective f hf_bij
  obtain ⟨a, ha⟩ := e.eq_linearEquivConjAlgEquiv
  refine ⟨a, ?_⟩
  intro X X' hX
  have hX' : X' = σ X := by
    apply w183b2_sigmaL_congr hT
    rw [← hX]
    exact w183b2_sigmaL_spec T h X
  rw [hX', ← ha]
  rfl

private noncomputable def w183b2_sigmaR (T : Module.End k (M ⊗[k] W))
    (h : ∀ X : Module.End k W, ∃ X' : Module.End k W,
      T * TensorProduct.map LinearMap.id X = TensorProduct.map LinearMap.id X' * T) :
    Module.End k W → Module.End k W :=
  fun X => (h X).choose

private lemma w183b2_sigmaR_spec (T : Module.End k (M ⊗[k] W))
    (h : ∀ X : Module.End k W, ∃ X' : Module.End k W,
      T * TensorProduct.map LinearMap.id X = TensorProduct.map LinearMap.id X' * T) (X) :
    T * TensorProduct.map LinearMap.id X =
      TensorProduct.map LinearMap.id (w183b2_sigmaR T h X) * T :=
  (h X).choose_spec

private lemma w183b2_sigmaR_congr {T : Module.End k (M ⊗[k] W)} (hT : IsUnit T) [Nontrivial M]
    {A B : Module.End k W}
    (hAB : TensorProduct.map LinearMap.id A * T = TensorProduct.map LinearMap.id B * T) :
    A = B :=
  w183b2_map_injective_right (hT.mul_right_cancel hAB)

private lemma w183b2_sigmaR_zero (T : Module.End k (M ⊗[k] W)) (hT : IsUnit T) [Nontrivial M]
    (h : ∀ X : Module.End k W, ∃ X' : Module.End k W,
      T * TensorProduct.map LinearMap.id X = TensorProduct.map LinearMap.id X' * T) :
    w183b2_sigmaR T h 0 = 0 := by
  apply w183b2_sigmaR_congr hT
  rw [← w183b2_sigmaR_spec T h 0]
  simp

private lemma w183b2_sigmaR_one (T : Module.End k (M ⊗[k] W)) (hT : IsUnit T) [Nontrivial M]
    (h : ∀ X : Module.End k W, ∃ X' : Module.End k W,
      T * TensorProduct.map LinearMap.id X = TensorProduct.map LinearMap.id X' * T) :
    w183b2_sigmaR T h 1 = 1 := by
  have hmap : TensorProduct.map (LinearMap.id : Module.End k M) (1 : Module.End k W) = 1 :=
    TensorProduct.map_id
  apply w183b2_sigmaR_congr hT
  rw [← w183b2_sigmaR_spec T h 1, hmap, mul_one, one_mul]

private lemma w183b2_sigmaR_add (T : Module.End k (M ⊗[k] W)) (hT : IsUnit T) [Nontrivial M]
    (h : ∀ X : Module.End k W, ∃ X' : Module.End k W,
      T * TensorProduct.map LinearMap.id X = TensorProduct.map LinearMap.id X' * T)
    (X Y : Module.End k W) :
    w183b2_sigmaR T h (X + Y) = w183b2_sigmaR T h X + w183b2_sigmaR T h Y := by
  apply w183b2_sigmaR_congr hT
  rw [← w183b2_sigmaR_spec T h (X + Y), TensorProduct.map_add_right, mul_add,
    w183b2_sigmaR_spec T h X, w183b2_sigmaR_spec T h Y, TensorProduct.map_add_right, add_mul]

private lemma w183b2_sigmaR_mul (T : Module.End k (M ⊗[k] W)) (hT : IsUnit T) [Nontrivial M]
    (h : ∀ X : Module.End k W, ∃ X' : Module.End k W,
      T * TensorProduct.map LinearMap.id X = TensorProduct.map LinearMap.id X' * T)
    (X Y : Module.End k W) :
    w183b2_sigmaR T h (X * Y) = w183b2_sigmaR T h X * w183b2_sigmaR T h Y := by
  apply w183b2_sigmaR_congr hT
  rw [← w183b2_sigmaR_spec T h (X * Y), w183b2_map_id_mul X Y]
  rw [w183b2_map_id_mul (w183b2_sigmaR T h X) (w183b2_sigmaR T h Y),
    ← mul_assoc, w183b2_sigmaR_spec T h X, mul_assoc, w183b2_sigmaR_spec T h Y, mul_assoc]

private lemma w183b2_sigmaR_smul (T : Module.End k (M ⊗[k] W)) (hT : IsUnit T) [Nontrivial M]
    (h : ∀ X : Module.End k W, ∃ X' : Module.End k W,
      T * TensorProduct.map LinearMap.id X = TensorProduct.map LinearMap.id X' * T)
    (r : k) (X : Module.End k W) :
    w183b2_sigmaR T h (r • X) = r • w183b2_sigmaR T h X := by
  apply w183b2_sigmaR_congr hT
  rw [← w183b2_sigmaR_spec T h (r • X), TensorProduct.map_smul_right, Algebra.mul_smul_comm,
    w183b2_sigmaR_spec T h X, TensorProduct.map_smul_right, Algebra.smul_mul_assoc]

private lemma w183b2_sigmaR_injective (T : Module.End k (M ⊗[k] W)) (hT : IsUnit T) [Nontrivial M]
    (h : ∀ X : Module.End k W, ∃ X' : Module.End k W,
      T * TensorProduct.map LinearMap.id X = TensorProduct.map LinearMap.id X' * T) :
    Function.Injective (w183b2_sigmaR T h) := by
  intro X Y hXY
  have h1 : T * TensorProduct.map LinearMap.id X = T * TensorProduct.map LinearMap.id Y := by
    rw [w183b2_sigmaR_spec T h X, hXY, ← w183b2_sigmaR_spec T h Y]
  exact w183b2_map_injective_right (hT.mul_left_cancel h1)

private lemma w183b2_exists_conj_of_normalizes_right [FiniteDimensional k W] [Nontrivial M]
    (T : Module.End k (M ⊗[k] W)) (hT : IsUnit T)
    (h : ∀ X : Module.End k W, ∃ X' : Module.End k W,
      T * TensorProduct.map LinearMap.id X = TensorProduct.map LinearMap.id X' * T) :
    ∃ a : W ≃ₗ[k] W, ∀ (X X' : Module.End k W),
      T * TensorProduct.map LinearMap.id X = TensorProduct.map LinearMap.id X' * T →
      X' = a.conjAlgEquiv k X := by
  let σ := w183b2_sigmaR T h
  let rh : Module.End k W →+* Module.End k W :=
    { toFun := σ
      map_one' := w183b2_sigmaR_one T hT h
      map_mul' := w183b2_sigmaR_mul T hT h
      map_zero' := w183b2_sigmaR_zero T hT h
      map_add' := w183b2_sigmaR_add T hT h }
  let f : Module.End k W →ₐ[k] Module.End k W :=
    AlgHom.mk' rh (fun r X => w183b2_sigmaR_smul T hT h r X)
  have hf_inj : Function.Injective f := w183b2_sigmaR_injective T hT h
  have hf_bij : Function.Bijective f :=
    ⟨hf_inj, LinearMap.surjective_of_injective (f := f.toLinearMap) hf_inj⟩
  let e : Module.End k W ≃ₐ[k] Module.End k W := AlgEquiv.ofBijective f hf_bij
  obtain ⟨a, ha⟩ := e.eq_linearEquivConjAlgEquiv
  refine ⟨a, ?_⟩
  intro X X' hX
  have hX' : X' = σ X := by
    apply w183b2_sigmaR_congr hT
    rw [← hX]
    exact w183b2_sigmaR_spec T h X
  rw [hX', ← ha]
  rfl

end InnerConj

theorem w183b2_tensor_normalizer [FiniteDimensional k U₁] [FiniteDimensional k U₂] [Nontrivial U₁]
    [Nontrivial U₂] (T : Module.End k (U₁ ⊗[k] U₂)) (hT : IsUnit T)
    (h₁ : ∀ X : Module.End k U₁, ∃ X' : Module.End k U₁,
      T * TensorProduct.map X LinearMap.id = TensorProduct.map X' LinearMap.id * T)
    (h₂ : ∀ Y : Module.End k U₂, ∃ Y' : Module.End k U₂,
      T * TensorProduct.map LinearMap.id Y = TensorProduct.map LinearMap.id Y' * T) :
    ∃ (a : Module.End k U₁) (b : Module.End k U₂), T = TensorProduct.map a b := by
  obtain ⟨a, ha⟩ := w183b2_exists_conj_of_normalizes (W := U₁) (M := U₂) T hT h₁
  obtain ⟨b, hb⟩ := w183b2_exists_conj_of_normalizes_right (W := U₂) (M := U₁) T hT h₂
  let S : U₁ ⊗[k] U₂ ≃ₗ[k] U₁ ⊗[k] U₂ := TensorProduct.congr a b
  let R : Module.End k (U₁ ⊗[k] U₂) :=
    (S.symm : U₁ ⊗[k] U₂ →ₗ[k] U₁ ⊗[k] U₂) * T
  have hs_mul : (S : Module.End k (U₁ ⊗[k] U₂)) *
      (S.symm : Module.End k (U₁ ⊗[k] U₂)) = 1 := by
    ext v; simp [Module.End.mul_apply]
  have hs_mul' : (S.symm : Module.End k (U₁ ⊗[k] U₂)) *
      (S : Module.End k (U₁ ⊗[k] U₂)) = 1 := by
    ext v; simp [Module.End.mul_apply]
  have ha_symm : (a.symm : Module.End k U₁) * (a : Module.End k U₁) = 1 := by
    ext v; simp [Module.End.mul_apply]
  have hb_symm : (b.symm : Module.End k U₂) * (b : Module.End k U₂) = 1 := by
    ext v; simp [Module.End.mul_apply]
  have hconja : ∀ X : Module.End k U₁,
      a.conjAlgEquiv k X = (a : Module.End k U₁) * X * (a.symm : Module.End k U₁) := by
    intro X
    rw [LinearEquiv.conjAlgEquiv_apply]
    ext v
    simp [Module.End.mul_apply, LinearMap.comp_apply]
  have hconjb : ∀ Y : Module.End k U₂,
      b.conjAlgEquiv k Y = (b : Module.End k U₂) * Y * (b.symm : Module.End k U₂) := by
    intro Y
    rw [LinearEquiv.conjAlgEquiv_apply]
    ext v
    simp [Module.End.mul_apply, LinearMap.comp_apply]
  have hSA : ∀ X : Module.End k U₁,
      (S : Module.End k (U₁ ⊗[k] U₂)) * TensorProduct.map X LinearMap.id =
        TensorProduct.map (a.conjAlgEquiv k X) LinearMap.id *
          (S : Module.End k (U₁ ⊗[k] U₂)) := by
    intro X
    change TensorProduct.map (a : U₁ →ₗ[k] U₁) (b : U₂ →ₗ[k] U₂) *
        TensorProduct.map X LinearMap.id =
      TensorProduct.map (a.conjAlgEquiv k X) LinearMap.id *
        TensorProduct.map (a : U₁ →ₗ[k] U₁) (b : U₂ →ₗ[k] U₂)
    simp only [← TensorProduct.map_mul]
    congr 1
    rw [hconja X, mul_assoc, ha_symm, mul_one]
  have hSB : ∀ Y : Module.End k U₂,
      (S : Module.End k (U₁ ⊗[k] U₂)) * TensorProduct.map LinearMap.id Y =
        TensorProduct.map LinearMap.id (b.conjAlgEquiv k Y) *
          (S : Module.End k (U₁ ⊗[k] U₂)) := by
    intro Y
    change TensorProduct.map (a : U₁ →ₗ[k] U₁) (b : U₂ →ₗ[k] U₂) *
        TensorProduct.map LinearMap.id Y =
      TensorProduct.map LinearMap.id (b.conjAlgEquiv k Y) *
        TensorProduct.map (a : U₁ →ₗ[k] U₁) (b : U₂ →ₗ[k] U₂)
    simp only [← TensorProduct.map_mul]
    congr 1
    rw [hconjb Y, mul_assoc, hb_symm, mul_one]
  have hRA : ∀ X : Module.End k U₁,
      R * TensorProduct.map X LinearMap.id = TensorProduct.map X LinearMap.id * R := by
    intro X
    obtain ⟨X', hX'⟩ := h₁ X
    have hX'a : X' = a.conjAlgEquiv k X := ha X X' hX'
    have hS := hSA X
    rw [hX'a] at hX'
    have hs : TensorProduct.map X LinearMap.id * (S.symm : Module.End k (U₁ ⊗[k] U₂)) =
        (S.symm : Module.End k (U₁ ⊗[k] U₂)) *
          TensorProduct.map (a.conjAlgEquiv k X) LinearMap.id := by
      have h1 : TensorProduct.map X LinearMap.id =
          ((S.symm : Module.End k (U₁ ⊗[k] U₂)) *
              TensorProduct.map (a.conjAlgEquiv k X) LinearMap.id) *
            (S : Module.End k (U₁ ⊗[k] U₂)) := by
        calc TensorProduct.map X LinearMap.id
            = ((S.symm : Module.End k (U₁ ⊗[k] U₂)) *
                (S : Module.End k (U₁ ⊗[k] U₂))) *
                TensorProduct.map X LinearMap.id := by rw [hs_mul', one_mul]
          _ = (S.symm : Module.End k (U₁ ⊗[k] U₂)) *
                ((S : Module.End k (U₁ ⊗[k] U₂)) * TensorProduct.map X LinearMap.id) :=
              mul_assoc _ _ _
          _ = (S.symm : Module.End k (U₁ ⊗[k] U₂)) *
                (TensorProduct.map (a.conjAlgEquiv k X) LinearMap.id *
                  (S : Module.End k (U₁ ⊗[k] U₂))) := by rw [hS]
          _ = ((S.symm : Module.End k (U₁ ⊗[k] U₂)) *
                TensorProduct.map (a.conjAlgEquiv k X) LinearMap.id) *
              (S : Module.End k (U₁ ⊗[k] U₂)) := (mul_assoc _ _ _).symm
      rw [h1, mul_assoc, hs_mul, mul_one]
    change (S.symm : Module.End k (U₁ ⊗[k] U₂)) * T * TensorProduct.map X LinearMap.id =
      TensorProduct.map X LinearMap.id * ((S.symm : Module.End k (U₁ ⊗[k] U₂)) * T)
    calc (S.symm : Module.End k (U₁ ⊗[k] U₂)) * T * TensorProduct.map X LinearMap.id
        = (S.symm : Module.End k (U₁ ⊗[k] U₂)) *
            (T * TensorProduct.map X LinearMap.id) := mul_assoc _ _ _
      _ = (S.symm : Module.End k (U₁ ⊗[k] U₂)) *
            (TensorProduct.map (a.conjAlgEquiv k X) LinearMap.id * T) := by rw [hX']
      _ = ((S.symm : Module.End k (U₁ ⊗[k] U₂)) *
            TensorProduct.map (a.conjAlgEquiv k X) LinearMap.id) * T := (mul_assoc _ _ _).symm
      _ = (TensorProduct.map X LinearMap.id * (S.symm : Module.End k (U₁ ⊗[k] U₂))) * T := by
            rw [← hs]
      _ = TensorProduct.map X LinearMap.id *
            ((S.symm : Module.End k (U₁ ⊗[k] U₂)) * T) := mul_assoc _ _ _
  have hRB : ∀ Y : Module.End k U₂,
      R * TensorProduct.map LinearMap.id Y = TensorProduct.map LinearMap.id Y * R := by
    intro Y
    obtain ⟨Y', hY'⟩ := h₂ Y
    have hY'b : Y' = b.conjAlgEquiv k Y := hb Y Y' hY'
    have hS := hSB Y
    rw [hY'b] at hY'
    have hs : TensorProduct.map LinearMap.id Y * (S.symm : Module.End k (U₁ ⊗[k] U₂)) =
        (S.symm : Module.End k (U₁ ⊗[k] U₂)) *
          TensorProduct.map LinearMap.id (b.conjAlgEquiv k Y) := by
      have h1 : TensorProduct.map LinearMap.id Y =
          ((S.symm : Module.End k (U₁ ⊗[k] U₂)) *
              TensorProduct.map LinearMap.id (b.conjAlgEquiv k Y)) *
            (S : Module.End k (U₁ ⊗[k] U₂)) := by
        calc TensorProduct.map LinearMap.id Y
            = ((S.symm : Module.End k (U₁ ⊗[k] U₂)) *
                (S : Module.End k (U₁ ⊗[k] U₂))) *
                TensorProduct.map LinearMap.id Y := by rw [hs_mul', one_mul]
          _ = (S.symm : Module.End k (U₁ ⊗[k] U₂)) *
                ((S : Module.End k (U₁ ⊗[k] U₂)) * TensorProduct.map LinearMap.id Y) :=
              mul_assoc _ _ _
          _ = (S.symm : Module.End k (U₁ ⊗[k] U₂)) *
                (TensorProduct.map LinearMap.id (b.conjAlgEquiv k Y) *
                  (S : Module.End k (U₁ ⊗[k] U₂))) := by rw [hS]
          _ = ((S.symm : Module.End k (U₁ ⊗[k] U₂)) *
                TensorProduct.map LinearMap.id (b.conjAlgEquiv k Y)) *
              (S : Module.End k (U₁ ⊗[k] U₂)) := (mul_assoc _ _ _).symm
      rw [h1, mul_assoc, hs_mul, mul_one]
    change (S.symm : Module.End k (U₁ ⊗[k] U₂)) * T * TensorProduct.map LinearMap.id Y =
      TensorProduct.map LinearMap.id Y * ((S.symm : Module.End k (U₁ ⊗[k] U₂)) * T)
    calc (S.symm : Module.End k (U₁ ⊗[k] U₂)) * T * TensorProduct.map LinearMap.id Y
        = (S.symm : Module.End k (U₁ ⊗[k] U₂)) *
            (T * TensorProduct.map LinearMap.id Y) := mul_assoc _ _ _
      _ = (S.symm : Module.End k (U₁ ⊗[k] U₂)) *
            (TensorProduct.map LinearMap.id (b.conjAlgEquiv k Y) * T) := by rw [hY']
      _ = ((S.symm : Module.End k (U₁ ⊗[k] U₂)) *
            TensorProduct.map LinearMap.id (b.conjAlgEquiv k Y)) * T := (mul_assoc _ _ _).symm
      _ = (TensorProduct.map LinearMap.id Y * (S.symm : Module.End k (U₁ ⊗[k] U₂))) * T := by
            rw [← hs]
      _ = TensorProduct.map LinearMap.id Y *
            ((S.symm : Module.End k (U₁ ⊗[k] U₂)) * T) := mul_assoc _ _ _
  have hpure : ∀ (X : Module.End k U₁) (Y : Module.End k U₂),
      R * TensorProduct.map X Y = TensorProduct.map X Y * R := by
    intro X Y
    have hmul : TensorProduct.map X Y =
        TensorProduct.map X LinearMap.id * TensorProduct.map LinearMap.id Y :=
      TensorProduct.map_comp X LinearMap.id LinearMap.id Y
    rw [hmul]
    calc R * (TensorProduct.map X LinearMap.id * TensorProduct.map LinearMap.id Y)
        = (R * TensorProduct.map X LinearMap.id) * TensorProduct.map LinearMap.id Y :=
          (mul_assoc R _ _).symm
      _ = (TensorProduct.map X LinearMap.id * R) * TensorProduct.map LinearMap.id Y := by
          rw [hRA X]
      _ = TensorProduct.map X LinearMap.id * (R * TensorProduct.map LinearMap.id Y) :=
          mul_assoc _ _ _
      _ = TensorProduct.map X LinearMap.id * (TensorProduct.map LinearMap.id Y * R) := by
          rw [hRB Y]
      _ = (TensorProduct.map X LinearMap.id * TensorProduct.map LinearMap.id Y) * R :=
          (mul_assoc _ _ _).symm
  have hRZ : ∀ Z : Module.End k (U₁ ⊗[k] U₂), R * Z = Z * R := by
    intro Z
    obtain ⟨t, ht⟩ := (homTensorHomEquiv k U₁ U₂ U₁ U₂).surjective Z
    have hmain : ∀ t : Module.End k U₁ ⊗[k] Module.End k U₂,
        R * (homTensorHomEquiv k U₁ U₂ U₁ U₂) t =
          (homTensorHomEquiv k U₁ U₂ U₁ U₂) t * R := by
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul X Y => simpa using hpure X Y
      | add x y hx hy => rw [map_add, mul_add, add_mul, hx, hy]
    rw [← ht]
    exact hmain t
  have hcenter : R ∈ Subalgebra.center k (Module.End k (U₁ ⊗[k] U₂)) :=
    Subalgebra.mem_center_iff.mpr (fun Z => (hRZ Z).symm)
  obtain ⟨c, _, hc⟩ := (Module.End.mem_subalgebraCenter_iff (R := k) (S := k)
    (M := U₁ ⊗[k] U₂)).mp hcenter
  have hc' : R = c • 1 := by
    rw [hc, Module.End.smulLeft_eq]
    rfl
  refine ⟨c • (a : Module.End k U₁), (b : Module.End k U₂), ?_⟩
  have hT_eq : T = (S : Module.End k (U₁ ⊗[k] U₂)) * R := by
    change T = (S : Module.End k (U₁ ⊗[k] U₂)) *
      ((S.symm : Module.End k (U₁ ⊗[k] U₂)) * T)
    rw [← mul_assoc, hs_mul, one_mul]
  rw [hT_eq, hc', Algebra.mul_smul_comm, mul_one, TensorProduct.map_smul_left]
  rfl

end CFSG.LocalAnalysis.WeakClosure81

end
