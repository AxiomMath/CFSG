module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType.ZS

open Subgroup

@[expose] noncomputable def owTr_conj {p : ℕ} {U V : Type} [AddCommGroup U] [Module (ZMod p) U]
    [AddCommGroup V] [Module (ZMod p) V] (e : U ≃ₗ[ZMod p] V) :
    (U ≃ₗ[ZMod p] U) →* (V ≃ₗ[ZMod p] V) where
  toFun g := e.symm.trans (g.trans e)
  map_one' := by
    ext v
    simp [LinearEquiv.trans_apply]
  map_mul' g h := by
    ext v
    simp [LinearEquiv.mul_apply, LinearEquiv.trans_apply]

@[simp] lemma owTr_conj_apply {p : ℕ} {U V : Type} [AddCommGroup U] [Module (ZMod p) U]
    [AddCommGroup V] [Module (ZMod p) V] (e : U ≃ₗ[ZMod p] V) (g : U ≃ₗ[ZMod p] U) :
    owTr_conj e g = e.symm.trans (g.trans e) := rfl

lemma owTr_conj_left_inv {p : ℕ} {U V : Type} [AddCommGroup U] [Module (ZMod p) U]
    [AddCommGroup V] [Module (ZMod p) V] (e : U ≃ₗ[ZMod p] V) (g : U ≃ₗ[ZMod p] U) :
    e.trans ((owTr_conj e g).trans e.symm) = g := by
  ext x
  simp [owTr_conj_apply, LinearEquiv.trans_apply]

lemma owTr_conj_injective {p : ℕ} {U V : Type} [AddCommGroup U] [Module (ZMod p) U]
    [AddCommGroup V] [Module (ZMod p) V] (e : U ≃ₗ[ZMod p] V) : Function.Injective (owTr_conj e) := by
  intro g h gh
  have h2 : e.trans ((owTr_conj e g).trans e.symm) = e.trans ((owTr_conj e h).trans e.symm) :=
    congrArg (fun f => e.trans (f.trans e.symm)) gh
  rw [owTr_conj_left_inv, owTr_conj_left_inv] at h2
  exact h2

lemma owTr_conj_sub_id_range {p : ℕ} {U V : Type} [AddCommGroup U] [Module (ZMod p) U]
    [AddCommGroup V] [Module (ZMod p) V] (e : U ≃ₗ[ZMod p] V) (g : U ≃ₗ[ZMod p] U) :
    LinearMap.range ((owTr_conj e g : V →ₗ[ZMod p] V) - (LinearMap.id : V →ₗ[ZMod p] V)) =
      Submodule.map e.toLinearMap
        (LinearMap.range ((g : U →ₗ[ZMod p] U) - (LinearMap.id : U →ₗ[ZMod p] U))) := by
  have hcomp : ((owTr_conj e g : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) =
      e.toLinearMap.comp ((g : U →ₗ[ZMod p] U).comp e.symm.toLinearMap) := by
    ext x
    simp [owTr_conj_apply, LinearEquiv.trans_apply]
  have hsub : e.toLinearMap.comp ((g : U →ₗ[ZMod p] U).comp e.symm.toLinearMap) -
        (LinearMap.id : V →ₗ[ZMod p] V) =
      e.toLinearMap.comp
        (((g : U →ₗ[ZMod p] U) - (LinearMap.id : U →ₗ[ZMod p] U)).comp e.symm.toLinearMap) := by
    ext x
    simp [LinearMap.comp_apply, LinearMap.sub_apply]
  rw [hcomp, hsub, LinearMap.range_comp]
  congr 1
  rw [LinearMap.range_comp, LinearMap.range_eq_top_of_surjective e.symm.toLinearMap e.symm.surjective,
    Submodule.map_top]

lemma owTr_conj_neg {p : ℕ} {U V : Type} [AddCommGroup U] [Module (ZMod p) U]
    [AddCommGroup V] [Module (ZMod p) V] (e : U ≃ₗ[ZMod p] V) :
    owTr_conj e (LinearEquiv.neg (ZMod p)) = LinearEquiv.neg (ZMod p) := by
  ext v
  simp [owTr_conj_apply, LinearEquiv.trans_apply, LinearEquiv.neg_apply]

lemma owTr_isRefl_conj {p : ℕ} {U V : Type} [AddCommGroup U] [Module (ZMod p) U]
    [AddCommGroup V] [Module (ZMod p) V] (e : U ≃ₗ[ZMod p] V) (g : U ≃ₗ[ZMod p] U) :
    IsRefl p g ↔ IsRefl p (owTr_conj e g) := by
  unfold IsRefl
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · calc owTr_conj e g * owTr_conj e g = owTr_conj e (g * g) := by rw [map_mul]
        _ = owTr_conj e 1 := by rw [h1]
        _ = 1 := map_one _
    · rw [owTr_conj_sub_id_range, LinearEquiv.finrank_map_eq]
      exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · apply owTr_conj_injective e
      rw [map_mul, map_one, h1]
    · rw [owTr_conj_sub_id_range, LinearEquiv.finrank_map_eq] at h2
      exact h2

lemma owTr_conj_phi_symm {p : ℕ} {U V : Type} [AddCommGroup U] [Module (ZMod p) U]
    [AddCommGroup V] [Module (ZMod p) V] (e : U ≃ₗ[ZMod p] V)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {A' : Subgroup (V ≃ₗ[ZMod p] V)} (φ : ↥A ≃* ↥A')
    (hφ : ∀ g : ↥A, ((φ g : ↥A') : V ≃ₗ[ZMod p] V) = e.symm.trans (((g : ↥A) : U ≃ₗ[ZMod p] U).trans e))
    {x' : ↥A'} :
    ((φ.symm x' : ↥A) : U ≃ₗ[ZMod p] U) = e.trans (((x' : ↥A') : V ≃ₗ[ZMod p] V).trans e.symm) := by
  have h := hφ (φ.symm x')
  rw [MulEquiv.apply_symm_apply] at h
  have h' : owTr_conj e ((φ.symm x' : ↥A) : U ≃ₗ[ZMod p] U) = ((x' : ↥A') : V ≃ₗ[ZMod p] V) := h.symm
  have h2 := congrArg (fun f => e.trans (f.trans e.symm)) h'
  rwa [owTr_conj_left_inv] at h2

theorem wit_linWeyl_transport {p : ℕ} {U V : Type} [AddCommGroup U] [Module (ZMod p) U]
    [AddCommGroup V] [Module (ZMod p) V] (e : U ≃ₗ[ZMod p] V)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {A' : Subgroup (V ≃ₗ[ZMod p] V)} (φ : ↥A ≃* ↥A')
    (hφ : ∀ g : ↥A, ((φ g : ↥A') : V ≃ₗ[ZMod p] V) = e.symm.trans (((g : ↥A) : U ≃ₗ[ZMod p] U).trans e))
    (h : LinWeyl p A') : LinWeyl p A := by
  obtain ⟨ι, M, hM, f, hf⟩ := h
  refine ⟨ι, M, hM, f.trans φ.symm, ?_⟩
  intro i
  have hs : IsRefl p ((f (M.simple i) : ↥A') : V ≃ₗ[ZMod p] V) := hf i
  have h_eq : (((f.trans φ.symm) (M.simple i) : ↥A) : U ≃ₗ[ZMod p] U) =
      owTr_conj e.symm ((f (M.simple i) : ↥A') : V ≃ₗ[ZMod p] V) := by
    simp only [MulEquiv.trans_apply]
    rw [owTr_conj_phi_symm e φ hφ]
    rw [owTr_conj_apply, LinearEquiv.symm_symm]
  rw [h_eq]
  exact (owTr_isRefl_conj (e := e.symm) ((f (M.simple i) : ↥A') : V ≃ₗ[ZMod p] V)).mp hs

theorem wit_neg3_transport {p : ℕ} {U V : Type} [AddCommGroup U] [Module (ZMod p) U]
    [AddCommGroup V] [Module (ZMod p) V] (e : U ≃ₗ[ZMod p] V)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {A' : Subgroup (V ≃ₗ[ZMod p] V)} (φ : ↥A ≃* ↥A')
    (hφ : ∀ g : ↥A, ((φ g : ↥A') : V ≃ₗ[ZMod p] V) = e.symm.trans (((g : ↥A) : U ≃ₗ[ZMod p] U).trans e))
    (h : WitNEG3 p A') : WitNEG3 p A := by
  obtain ⟨hfin, hmem⟩ := h
  refine ⟨?_, ?_⟩
  · rw [LinearEquiv.finrank_eq e]
    exact hfin
  · let x' : ↥A' := ⟨(LinearEquiv.neg (ZMod p) : V ≃ₗ[ZMod p] V), hmem⟩
    let y : ↥A := φ.symm x'
    have hy : ((y : ↥A) : U ≃ₗ[ZMod p] U) = (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) := by
      have hx' : ((φ y : ↥A') : V ≃ₗ[ZMod p] V) = (LinearEquiv.neg (ZMod p) : V ≃ₗ[ZMod p] V) := by
        have h1 : φ y = x' := MulEquiv.apply_symm_apply φ x'
        rw [h1]
      have hφy := hφ y
      rw [hφy] at hx'
      rw [← owTr_conj_neg e] at hx'
      exact owTr_conj_injective e hx'
    rw [← hy]
    exact y.property

end CFSG.StandardType.ZS

end
