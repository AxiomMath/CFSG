module

public import CFSG.Quasithin.H13.U3Basic
public import Mathlib.RingTheory.Coalgebra.CoassocSimps

public section

namespace CFSG.Quasithin.H13.U3

open CFSG.Quasithin.SteinbergCB Module

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module (ZMod 2) V₁] [AddCommGroup V₂]
  [Module (ZMod 2) V₂]

@[expose] def linConj (Φ : V₁ ≃ₗ[ZMod 2] V₂) : (V₁ ≃ₗ[ZMod 2] V₁) ≃* (V₂ ≃ₗ[ZMod 2] V₂) where
  toFun g := Φ.symm.trans (g.trans Φ)
  invFun h := Φ.trans (h.trans Φ.symm)
  left_inv g := by ext x; simp
  right_inv h := by ext x; simp
  map_mul' g h := by ext x; simp

theorem linConj_apply (Φ : V₁ ≃ₗ[ZMod 2] V₂) (g : V₁ ≃ₗ[ZMod 2] V₁) (x : V₂) :
    linConj Φ g x = Φ (g (Φ.symm x)) :=
  rfl

theorem linConj_symm_apply (Φ : V₁ ≃ₗ[ZMod 2] V₂) (h : V₂ ≃ₗ[ZMod 2] V₂) (x : V₁) :
    (linConj Φ).symm h x = Φ.symm (h (Φ x)) :=
  rfl

theorem linFix_map_linConj (Φ : V₁ ≃ₗ[ZMod 2] V₂) (E : Subgroup (V₁ ≃ₗ[ZMod 2] V₁)) :
    linFix (E.map (linConj Φ).toMonoidHom) = (linFix E).map (Φ : V₁ →ₗ[ZMod 2] V₂) := by
  ext x
  rw [mem_linFix_iff, Submodule.mem_map_equiv, mem_linFix_iff]
  constructor
  · intro h g hg
    have := h _ ⟨g, hg, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, linConj_apply] at this
    rw [← Φ.symm_apply_apply (g (Φ.symm x)), this]
  · rintro h _ ⟨g, hg, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, linConj_apply, h g hg, LinearEquiv.apply_symm_apply]

theorem linComm_map_linConj (Φ : V₁ ≃ₗ[ZMod 2] V₂) (E : Subgroup (V₁ ≃ₗ[ZMod 2] V₁)) :
    linComm (E.map (linConj Φ).toMonoidHom) = (linComm E).map (Φ : V₁ →ₗ[ZMod 2] V₂) := by
  rw [linComm, linComm, Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, x, rfl⟩
    refine ⟨g (Φ.symm x) - Φ.symm x, ⟨g, hg, Φ.symm x, rfl⟩, ?_⟩
    rw [LinearEquiv.coe_coe, map_sub, LinearEquiv.apply_symm_apply, MulEquiv.coe_toMonoidHom,
      linConj_apply]
  · rintro ⟨_, ⟨g, hg, x, rfl⟩, rfl⟩
    refine ⟨linConj Φ g, ⟨g, hg, rfl⟩, Φ x, ?_⟩
    rw [LinearEquiv.coe_coe, map_sub, linConj_apply, LinearEquiv.symm_apply_apply]

theorem linRank_linConj (Φ : V₁ ≃ₗ[ZMod 2] V₂) (g : V₁ ≃ₗ[ZMod 2] V₁) :
    linRank (linConj Φ g) = linRank g := by
  rw [linRank, linRank]
  have h : LinearMap.range (((linConj Φ g : V₂ ≃ₗ[ZMod 2] V₂) : V₂ →ₗ[ZMod 2] V₂) -
      LinearMap.id) = (LinearMap.range ((g : V₁ →ₗ[ZMod 2] V₁) - LinearMap.id)).map
        (Φ : V₁ →ₗ[ZMod 2] V₂) := by
    ext y
    simp only [LinearMap.mem_range, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      Submodule.mem_map, linConj_apply]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨g (Φ.symm x) - Φ.symm x, ⟨Φ.symm x, rfl⟩, by
        rw [map_sub, LinearEquiv.apply_symm_apply]⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨Φ x, by rw [LinearEquiv.symm_apply_apply, map_sub]⟩
  rw [h, LinearEquiv.finrank_map_eq]

theorem orderOf_linConj (Φ : V₁ ≃ₗ[ZMod 2] V₂) (g : V₁ ≃ₗ[ZMod 2] V₁) :
    orderOf (linConj Φ g) = orderOf g :=
  MulEquiv.orderOf_eq _ g

@[expose] def HyperCond {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (E : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  ∀ B : Subgroup (V ≃ₗ[ZMod 2] V), B ≤ E → B.relIndex E = 2 → linFix B = linFix E

@[expose] def ElemConclusion {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (E : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  Nat.card E = 8 ∧ linFix E = linComm E ∧ finrank (ZMod 2) (linFix E) = 3 ∧
    ∃ e ∈ E, e ≠ 1 ∧ linRank e = 2

theorem hyperCond_map_linConj (Φ : V₁ ≃ₗ[ZMod 2] V₂) {E : Subgroup (V₁ ≃ₗ[ZMod 2] V₁)}
    (hH : HyperCond E) : HyperCond (E.map (linConj Φ).toMonoidHom) := by
  set f := (linConj Φ).toMonoidHom with hf
  have hfinj : Function.Injective f := (linConj Φ).injective
  intro B' hB' hidx
  set B := B'.comap f with hB
  have hBmap : B.map f = B' :=
    Subgroup.map_comap_eq_self (hB'.trans (Subgroup.map_le_range _ _))
  have hBE : B ≤ E := by
    intro x hx
    have hx' : f x ∈ E.map f := hB' hx
    obtain ⟨y, hy, hyx⟩ := hx'
    rw [hfinj hyx] at hy
    exact hy
  have hidx' : B.relIndex E = 2 := by
    have h1 : (B.map f).relIndex (E.map f) = B.relIndex E :=
      Subgroup.relIndex_map_map_of_injective _ _ hfinj
    rw [hBmap] at h1
    rw [← h1]
    exact hidx
  have := hH B hBE hidx'
  rw [← hBmap, hf, linFix_map_linConj, linFix_map_linConj, this]

theorem elemConclusion_of_map_linConj (Φ : V₁ ≃ₗ[ZMod 2] V₂) {E : Subgroup (V₁ ≃ₗ[ZMod 2] V₁)}
    (h : ElemConclusion (E.map (linConj Φ).toMonoidHom)) : ElemConclusion E := by
  have hfinj : Function.Injective (linConj Φ).toMonoidHom := (linConj Φ).injective
  obtain ⟨hcard, hfc, hrk, e', he', he'1, he'rk⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hcard, Subgroup.card_map_of_injective hfinj]
  · rw [linFix_map_linConj, linComm_map_linConj] at hfc
    exact Submodule.map_injective_of_injective Φ.injective hfc
  · rw [← hrk, linFix_map_linConj, LinearEquiv.finrank_map_eq]
  · obtain ⟨e, he, rfl⟩ := he'
    refine ⟨e, he, ?_, ?_⟩
    · rintro rfl
      exact he'1 (map_one _)
    · rw [← he'rk]
      exact (linRank_linConj Φ e).symm

theorem qtBinarySixProfile_of_map_linConj (Φ : V₁ ≃ₗ[ZMod 2] V₂)
    (b : LinearMap.BilinForm (ZMod 2) V₂) (Γ : Subgroup (V₁ ≃ₗ[ZMod 2] V₁))
    (h : QTBinarySixProfile b (Γ.map (linConj Φ).toMonoidHom)) :
    QTBinarySixProfile (b.compl₁₂ (Φ : V₁ →ₗ[ZMod 2] V₂) (Φ : V₁ →ₗ[ZMod 2] V₂)) Γ := by
  obtain ⟨hdim, hnd, halt, hinv, hrank, hprof⟩ := h
  set f := (linConj Φ).toMonoidHom with hf
  have hfinj : Function.Injective f := (linConj Φ).injective
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [LinearEquiv.finrank_eq Φ, hdim]
  · have heq : b.compl₁₂ (Φ : V₁ →ₗ[ZMod 2] V₂) (Φ : V₁ →ₗ[ZMod 2] V₂) =
        LinearMap.BilinForm.congr Φ.symm b := by
      ext x y
      simp [LinearMap.BilinForm.congr_apply]
    rw [heq, LinearMap.BilinForm.nondegenerate_congr_iff]
    exact hnd
  · intro x
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe]
    exact halt (Φ x)
  · intro g hg x y
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe]
    have := hinv (linConj Φ g) ⟨g, hg, rfl⟩ (Φ x) (Φ y)
    rwa [linConj_apply, linConj_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply] at this
  · intro e he hord
    have := hrank (linConj Φ e) ⟨e, he, rfl⟩ (by rw [orderOf_linConj, hord])
    rwa [linRank_linConj] at this
  · intro E hEΓ hE1 hEab hH
    have hE'1 : E.map f ≠ ⊥ := by
      rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hfinj]
      exact hE1
    have hE'ab : CFSG.IsElementaryAbelian 2 (E.map f) := by
      have := hEab
      exact IsElementaryAbelian.map _
    exact elemConclusion_of_map_linConj Φ
      (hprof _ (Subgroup.map_mono hEΓ) hE'1 hE'ab (hyperCond_map_linConj Φ hH))

end CFSG.Quasithin.H13.U3
