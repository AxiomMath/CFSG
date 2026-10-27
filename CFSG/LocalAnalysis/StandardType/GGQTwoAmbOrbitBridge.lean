module

public import CFSG.LocalAnalysis.StandardType.GGQTwoAmbModelBridge
public import CFSG.LocalAnalysis.StandardType.GGQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGLineStabNormalizes

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

namespace GGQTwoAmbModel

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
  {L H : Subgroup G}

@[expose] noncomputable def linGroup (M : GGQTwoAmbModel p Bs x y L H) :
    Subgroup (M.V ≃ₗ[ZMod p] M.V) :=
  (ggAutomizer ⊤ Bs).map (ggLin (p := p) M.model)

theorem weyl_le_lin (M : GGQTwoAmbModel p Bs x y L H) : M.toLin.weyl ≤ M.linGroup :=
  M.weyl_le.trans (Subgroup.map_mono (ggAutomizer_mono Bs le_top))

theorem transvectionFree [Finite G] (M : GGQTwoAmbModel p Bs x y L H)
    (hNT : GGNoTransvection p Bs) : TransvectionFree M.linGroup := by
  rintro g hg ⟨u, ψ, hu, hψ, hψu, hgv⟩
  rw [linGroup] at hg
  obtain ⟨φ, hφ, rfl⟩ := hg
  have hφ' : φ ∈ ggInduced ⊤ Bs := by
    rw [ggAutomizer_eq] at hφ
    exact hφ
  exact hNT φ hφ' (ggIsTransvection_of_apply M.model hu hψ hψu hgv)

theorem reflGp_map [Finite G] (M : GGQTwoAmbModel p Bs x y L H) (hp2 : p ≠ 2) :
    (ggReflGp p Bs).map (ggLin (p := p) M.model) = reflGp M.linGroup := by
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have hST : ggLin (p := p) M.model '' {φ | φ ∈ ggAutomizer ⊤ Bs ∧ GGIsReflection p φ} =
      {t | t ∈ M.linGroup ∧ IsReflLin t} := by
    ext t
    constructor
    · rintro ⟨φ, ⟨hφA, hφr⟩, hφt⟩
      refine ⟨?_, ?_⟩
      · rw [linGroup]
        exact Subgroup.mem_map.mpr ⟨φ, hφA, hφt⟩
      · obtain ⟨c, f, hcf, hφc⟩ := exists_of_ggIsReflection (p := p) M.model hφr
        exact ⟨c, f, hcf, hφt.symm.trans (ggLin_eq_reflection M.model hcf hφc)⟩
    · rintro ⟨htlin, ht⟩
      rw [linGroup] at htlin
      obtain ⟨φ, hφA, hφt⟩ := htlin
      obtain ⟨c, g, hg, ht_eq⟩ := ht
      exact ⟨φ, ⟨hφA, ggIsReflection_of_eq_reflection hp2 M.model hg (hφt.trans ht_eq)⟩, hφt⟩
  rw [ggReflGp, reflGp, MonoidHom.map_closure, hST]

private lemma model_nsmul' (M : GGQTwoAmbModel p Bs x y L H) (n : ℕ) (b : ↥Bs) :
    M.model (n • Additive.ofMul b) = n • M.model (Additive.ofMul b) :=
  (M.model.toAddMonoidHom).map_nsmul n (Additive.ofMul b)

private lemma model_zsmul' (M : GGQTwoAmbModel p Bs x y L H) (n : ℤ) (b : ↥Bs) :
    M.model (n • Additive.ofMul b) = n • M.model (Additive.ofMul b) :=
  (M.model.toAddMonoidHom).map_zsmul n (Additive.ofMul b)

theorem zpowers_iff_span (M : GGQTwoAmbModel p Bs x y L H) (a b : ↥Bs) :
    Subgroup.zpowers a = Subgroup.zpowers b ↔
      Submodule.span (ZMod p) {M.model (Additive.ofMul a)} =
        Submodule.span (ZMod p) {M.model (Additive.ofMul b)} := by
  have key : ∀ c d : ↥Bs, c ∈ Subgroup.zpowers d →
      M.model (Additive.ofMul c) ∈ Submodule.span (ZMod p) {M.model (Additive.ofMul d)} := by
    intro c d h
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [← hm, ofMul_zpow]
    rw [model_zsmul' M m d]
    rw [← Int.cast_smul_eq_zsmul (R := ZMod p)]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have key' : ∀ c d : ↥Bs,
      M.model (Additive.ofMul c) ∈ Submodule.span (ZMod p) {M.model (Additive.ofMul d)} →
      c ∈ Subgroup.zpowers d := by
    intro c d h
    rw [Submodule.mem_span_singleton] at h
    obtain ⟨k, hk⟩ := h
    rw [← ZMod.natCast_zmod_val k, Nat.cast_smul_eq_nsmul,
      ← model_nsmul' M k.val d, ← ofMul_pow] at hk
    have h2 : Additive.ofMul (d ^ k.val) = Additive.ofMul c := M.model.injective hk
    have h3 : d ^ k.val = c := Additive.ofMul.injective h2
    rw [← h3]
    exact Subgroup.npow_mem_zpowers d k.val
  constructor
  · intro h
    have hab : a ∈ Subgroup.zpowers b := by rw [← h]; exact Subgroup.mem_zpowers a
    have hba : b ∈ Subgroup.zpowers a := by rw [h]; exact Subgroup.mem_zpowers b
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact key a b hab
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact key b a hba
  · intro h
    have hab : M.model (Additive.ofMul a) ∈
        Submodule.span (ZMod p) {M.model (Additive.ofMul b)} := by
      rw [← h]; exact Submodule.mem_span_singleton_self _
    have hba : M.model (Additive.ofMul b) ∈
        Submodule.span (ZMod p) {M.model (Additive.ofMul a)} := by
      rw [h]; exact Submodule.mem_span_singleton_self _
    refine le_antisymm ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact key' a b hab
    · rw [Subgroup.zpowers_le]
      exact key' b a hba

theorem orbit_iff [Finite G] (M : GGQTwoAmbModel p Bs x y L H) (hp2 : p ≠ 2) (u : ↥Bs) :
    GGOrbitStableAt p Bs u ↔ ∀ φ ∈ M.linGroup, ∃ r ∈ reflGp M.linGroup,
      Submodule.span (ZMod p) {φ (M.model (Additive.ofMul u))} =
        Submodule.span (ZMod p) {r (M.model (Additive.ofMul u))} := by
  constructor
  · intro h φ hφ
    rw [linGroup, Subgroup.mem_map] at hφ
    obtain ⟨φa, hφa, rfl⟩ := hφ
    obtain ⟨ra, hra, hz⟩ := h φa hφa
    refine ⟨ggLin (p := p) M.model ra, ?_, ?_⟩
    · rw [← M.reflGp_map hp2, Subgroup.mem_map]
      exact ⟨ra, hra, rfl⟩
    · rw [ggLin_apply_ofMul, ggLin_apply_ofMul]
      exact (M.zpowers_iff_span (φa u) (ra u)).mp hz
  · intro h φ hφ
    have hφ' : ggLin (p := p) M.model φ ∈ M.linGroup := by
      rw [linGroup, Subgroup.mem_map]
      exact ⟨φ, hφ, rfl⟩
    obtain ⟨r, hr, hsp⟩ := h (ggLin (p := p) M.model φ) hφ'
    rw [← M.reflGp_map hp2, Subgroup.mem_map] at hr
    obtain ⟨ra, hra, rfl⟩ := hr
    refine ⟨ra, hra, ?_⟩
    rw [ggLin_apply_ofMul, ggLin_apply_ofMul] at hsp
    exact (M.zpowers_iff_span (φ u) (ra u)).mpr hsp

private theorem mem_zpowers_of_smul' (M : GGQTwoAmbModel p Bs x y L H) (ψ : MulAut ↥Bs)
    (c : ZMod p)
    (h : ggLin (p := p) M.model ψ (M.model (Additive.ofMul ⟨x, M.hx⟩)) =
      c • M.model (Additive.ofMul ⟨x, M.hx⟩)) :
    ψ ⟨x, M.hx⟩ ∈ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine Subgroup.mem_zpowers_iff.mpr ⟨(c.val : ℤ), ?_⟩
  rw [zpow_natCast]
  have h2 : Additive.ofMul (ψ ⟨x, M.hx⟩) = Additive.ofMul (⟨x, M.hx⟩ ^ c.val) := by
    apply M.model.injective
    rw [← ggLin_apply_ofMul (p := p) M.model ψ ⟨x, M.hx⟩, h]
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    rw [Nat.cast_smul_eq_nsmul, ofMul_pow, map_nsmul]
  exact (Additive.ofMul.injective h2).symm

theorem HL_lin [Finite G] {B D J : Subgroup G} (hHL : GGLineStabNormalizesInput)
    (hS : GGQTwoSetting p B Bs x L D J) (M : GGQTwoAmbModel p Bs x y L H) :
    ∀ φ ∈ M.linGroup, φ M.xV ∈ Submodule.span (ZMod p) {M.xV} →
      φ ∈ Subgroup.normalizer (M.parabL {k | k ≠ M.a} : Set (M.V ≃ₗ[ZMod p] M.V)) := by
  intro φ hφ hfixspan
  obtain ⟨ψ, hψ, hφψ⟩ := Subgroup.mem_map.mp hφ
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hfixspan
  have hfixψ : ψ ⟨x, M.hx⟩ ∈ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) := by
    refine M.mem_zpowers_of_smul' ψ c ?_
    rw [hφψ]
    simpa only [GGQTwoAmbModel.xV] using hc.symm
  have hψN : ψ ∈ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs)) :=
    hHL G p B Bs x L D J hS.1 M.hx ψ hψ hfixψ
  have hnorm : ggLin (p := p) M.model ψ ∈
      Subgroup.normalizer ((ggAutomizer L Bs).map (ggLin (p := p) M.model)) :=
    Subgroup.le_normalizer_map (ggLin (p := p) M.model) ⟨ψ, hψN, rfl⟩
  rw [hφψ, ← M.parabL_L] at hnorm
  exact hnorm

theorem D_eq_span [Finite G] {B D J K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (M : GGQTwoAmbModel p Bs x y L H) :
    ∀ v : M.V, v ∈ Submodule.span (ZMod p) {M.xV, M.yV} ↔
      ∃ d : ↥Bs, (d : G) ∈ D ∧ M.model (Additive.ofMul d) = v := by
  have hD : D = Subgroup.closure ({x, y} : Set G) := hnb.2.1
  subst hD
  intro v
  constructor
  · intro hv
    refine ⟨Additive.toMul (M.model.symm v), ?_, ?_⟩
    · rw [M.mem_closure_iff,
        show Additive.ofMul (Additive.toMul (M.model.symm v)) = M.model.symm v from
          Equiv.apply_symm_apply Additive.ofMul (M.model.symm v),
        AddEquiv.apply_symm_apply M.model v]
      exact hv
    · rw [show Additive.ofMul (Additive.toMul (M.model.symm v)) = M.model.symm v from
          Equiv.apply_symm_apply Additive.ofMul (M.model.symm v)]
      exact AddEquiv.apply_symm_apply M.model v
  · rintro ⟨d, hd, rfl⟩
    exact (M.mem_closure_iff d).mp hd

theorem card_L (M : GGQTwoAmbModel p Bs x y L H) :
    Nat.card (ggAutomizer L Bs) = Nat.card (M.parabL {k | k ≠ M.a}) := by
  rw [M.parabL_L]
  exact Nat.card_congr (Subgroup.equivMapOfInjective (ggAutomizer L Bs)
    (ggLin (p := p) M.model) (ggLin_injective M.model)).toEquiv

end GGQTwoAmbModel

end CFSG.StandardType

end
