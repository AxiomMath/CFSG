module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoTransport

public section

namespace CFSG.StandardType.HdRo7SU.Small

open CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7SmBridgeAux_symm {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') : (ggLinConj τ).symm = ggLinConj τ.symm := by
  ext g
  rfl

private lemma hdRo7SmBridgeAux_move {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') (g : V ≃ₗ[ZMod p] V) :
    LinearMap.range ((ggLinConj τ g : V' →ₗ[ZMod p] V') - LinearMap.id) =
      (LinearMap.range ((g : V →ₗ[ZMod p] V) - LinearMap.id)).map
        (τ : V →ₗ[ZMod p] V') := by
  have hcomp : ((ggLinConj τ g : V' →ₗ[ZMod p] V') - LinearMap.id) =
      (τ : V →ₗ[ZMod p] V').comp
        (((g : V →ₗ[ZMod p] V) - LinearMap.id).comp (τ.symm : V' →ₗ[ZMod p] V)) := by
    ext v
    simp [ggLinConj_apply, map_sub]
  rw [hcomp, LinearMap.range_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr τ.symm.surjective, Submodule.map_top]

private lemma hdRo7SmBridgeAux_isRefl {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') (g : V ≃ₗ[ZMod p] V) :
    ZS.IsRefl p (ggLinConj τ g) ↔ ZS.IsRefl p g := by
  have hmove := hdRo7SmBridgeAux_move τ g
  have hfin : Module.finrank (ZMod p)
        (LinearMap.range ((ggLinConj τ g : V' →ₗ[ZMod p] V') - LinearMap.id)) =
      Module.finrank (ZMod p)
        (LinearMap.range ((g : V →ₗ[ZMod p] V) - LinearMap.id)) := by
    rw [hmove, LinearEquiv.finrank_map_eq]
  constructor
  · rintro ⟨h2, hr⟩
    refine ⟨?_, by rwa [hfin] at hr⟩
    have h2' : ggLinConj τ (g * g) = ggLinConj τ 1 := by
      rw [map_mul, map_one, h2]
    exact (ggLinConj τ).injective h2'
  · rintro ⟨h2, hr⟩
    refine ⟨?_, by rwa [hfin]⟩
    rw [← map_mul, ← map_one (ggLinConj τ), h2]

private noncomputable def hdRo7SmBridgeAux_mapEquiv {p : ℕ} [Fact p.Prime] {V V' : Type}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') (H : Subgroup (V ≃ₗ[ZMod p] V)) :
    ↥H ≃* ↥(H.map (ggLinConj τ).toMonoidHom) where
  toFun h := ⟨ggLinConj τ (h : V ≃ₗ[ZMod p] V), Subgroup.mem_map.mpr ⟨_, h.2, rfl⟩⟩
  invFun x := ⟨(ggLinConj τ).symm (x : V' ≃ₗ[ZMod p] V'), by
    refine (Subgroup.mem_map_iff_mem (f := (ggLinConj τ).toMonoidHom)
      (ggLinConj τ).injective).mp ?_
    simpa using x.2⟩
  left_inv h := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_mul' h k := by
    apply Subtype.ext
    show ggLinConj τ ((h : V ≃ₗ[ZMod p] V) * (k : V ≃ₗ[ZMod p] V)) =
      ggLinConj τ (h : V ≃ₗ[ZMod p] V) * ggLinConj τ (k : V ≃ₗ[ZMod p] V)
    rw [map_mul]

private lemma hdRo7SmBridgeAux_mapEquiv_apply {p : ℕ} [Fact p.Prime] {V V' : Type}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') (H : Subgroup (V ≃ₗ[ZMod p] V)) (h : ↥H) :
    ((hdRo7SmBridgeAux_mapEquiv τ H h : ↥(H.map (ggLinConj τ).toMonoidHom)) :
      V' ≃ₗ[ZMod p] V') = ggLinConj τ (h : V ≃ₗ[ZMod p] V) := rfl

private lemma hdRo7SmBridgeAux_mapEquiv_symm_apply {p : ℕ} [Fact p.Prime] {V V' : Type}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') (H : Subgroup (V ≃ₗ[ZMod p] V))
    (x : ↥(H.map (ggLinConj τ).toMonoidHom)) :
    (((hdRo7SmBridgeAux_mapEquiv τ H).symm x : ↥H) : V ≃ₗ[ZMod p] V) =
      ggLinConj τ.symm (x : V' ≃ₗ[ZMod p] V') := by
  change ((ggLinConj τ).symm (x : V' ≃ₗ[ZMod p] V') : V ≃ₗ[ZMod p] V) =
    ggLinConj τ.symm (x : V' ≃ₗ[ZMod p] V')
  rw [hdRo7SmBridgeAux_symm]

theorem linWeyl_of_map_ggLinConj {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V'] (τ : V ≃ₗ[ZMod p] V')
    (H : Subgroup (V ≃ₗ[ZMod p] V))
    (h : ZS.LinWeyl p (H.map (ggLinConj τ).toMonoidHom)) : ZS.LinWeyl p H := by
  obtain ⟨ι, M, hM, f, hf⟩ := h
  refine ⟨ι, M, hM, f.trans (hdRo7SmBridgeAux_mapEquiv τ H).symm, fun i => ?_⟩
  change ZS.IsRefl p
    (((hdRo7SmBridgeAux_mapEquiv τ H).symm (f (M.simple i)) : ↥H) : V ≃ₗ[ZMod p] V)
  rw [hdRo7SmBridgeAux_mapEquiv_symm_apply]
  exact (hdRo7SmBridgeAux_isRefl τ.symm _).mpr (hf i)

theorem linWeyl_map_ggLinConj {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V'] (τ : V ≃ₗ[ZMod p] V')
    (H : Subgroup (V ≃ₗ[ZMod p] V)) (h : ZS.LinWeyl p H) :
    ZS.LinWeyl p (H.map (ggLinConj τ).toMonoidHom) := by
  obtain ⟨ι, M, hM, f, hf⟩ := h
  refine ⟨ι, M, hM, f.trans (hdRo7SmBridgeAux_mapEquiv τ H), fun i => ?_⟩
  change ZS.IsRefl p
    (((hdRo7SmBridgeAux_mapEquiv τ H (f (M.simple i)) :
      ↥(H.map (ggLinConj τ).toMonoidHom)) : V' ≃ₗ[ZMod p] V'))
  rw [hdRo7SmBridgeAux_mapEquiv_apply]
  exact (hdRo7SmBridgeAux_isRefl τ _).mpr (hf i)

theorem c2Transv_of_isTransvectionLin {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (g : V ≃ₗ[ZMod p] V) (hg : QTwoLin.IsTransvectionLin g) :
    C2Transv p g := by
  obtain ⟨u, ψ, _hu, hψ, hψu, hg⟩ := hg
  refine ⟨?_, ?_⟩
  · have hmove : ggLinMove g = Submodule.span (ZMod p) {u} := by
      rw [ggLinMove]
      apply le_antisymm
      · rintro x ⟨v, rfl⟩
        change g v - v ∈ Submodule.span (ZMod p) {u}
        have hv : v + ψ v • u - v = ψ v • u := by abel
        rw [hg v, hv]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))
      · rw [Submodule.span_le]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        obtain ⟨w, hw⟩ : ∃ w, ψ w ≠ 0 := by
          by_contra h
          apply hψ
          ext v
          by_contra hv
          exact h ⟨v, hv⟩
        refine (LinearMap.mem_range (f := (g : V →ₗ[ZMod p] V) - LinearMap.id)).mpr ?_
        refine ⟨(ψ w)⁻¹ • w, ?_⟩
        rw [LinearMap.sub_apply, LinearMap.id_apply, map_smul]
        change (ψ w)⁻¹ • g w - (ψ w)⁻¹ • w = x
        rw [hg w, smul_add, smul_smul, inv_mul_cancel₀ hw, one_smul]
        abel
    rw [hmove]
    exact finrank_span_singleton _hu
  · intro w
    have h1 : g w - w = ψ w • u := by
      rw [hg w]
      abel
    calc g (g w - w) = g (ψ w • u) := by rw [h1]
      _ = ψ w • g u := by rw [map_smul]
      _ = ψ w • u := by rw [hg u, hψu, zero_smul, add_zero]
      _ = g w - w := h1.symm

end CFSG.StandardType.HdRo7SU.Small

end
