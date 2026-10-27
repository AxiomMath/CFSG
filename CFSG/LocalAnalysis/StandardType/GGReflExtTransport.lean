module

public import CFSG.LocalAnalysis.StandardType.GGReflExtSound

public section

namespace CFSG.ReflExt

open CFSG.TwoNodeSmall CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def rxConj {p : ℕ} [Fact p.Prime] {V W : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [AddCommGroup W] [Module (ZMod p) W] (e : V ≃ₗ[ZMod p] W) :
    (V ≃ₗ[ZMod p] V) ≃* (W ≃ₗ[ZMod p] W) where
  toFun g := e.symm.trans (g.trans e)
  invFun h := e.trans (h.trans e.symm)
  left_inv g := by
    apply LinearEquiv.ext
    intro v
    simp [LinearEquiv.trans_apply]
  right_inv h := by
    apply LinearEquiv.ext
    intro w
    simp [LinearEquiv.trans_apply]
  map_mul' g h := by
    apply LinearEquiv.ext
    intro w
    simp [LinearEquiv.trans_apply]

theorem rxConj_apply {p : ℕ} [Fact p.Prime] {V W : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [AddCommGroup W] [Module (ZMod p) W] (e : V ≃ₗ[ZMod p] W) (g : V ≃ₗ[ZMod p] V) (w : W) :
    rxConj e g w = e (g (e.symm w)) := rfl

theorem rxConj_sub_id {p : ℕ} [Fact p.Prime] {V W : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [AddCommGroup W] [Module (ZMod p) W] (e : V ≃ₗ[ZMod p] W) (g : V ≃ₗ[ZMod p] V) :
    ((rxConj e g : W ≃ₗ[ZMod p] W) : W →ₗ[ZMod p] W) - LinearMap.id =
      e.toLinearMap.comp (((g : V →ₗ[ZMod p] V) - LinearMap.id).comp e.symm.toLinearMap) := by
  ext w
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
    LinearEquiv.coe_toLinearMap, rxConj_apply, map_sub, LinearEquiv.apply_symm_apply]

theorem rxConj_move {p : ℕ} [Fact p.Prime] {V W : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [AddCommGroup W] [Module (ZMod p) W] (e : V ≃ₗ[ZMod p] W) (g : V ≃ₗ[ZMod p] V) :
    ggLinMove (rxConj e g) = Submodule.map e.toLinearMap (ggLinMove g) := by
  unfold ggLinMove
  rw [rxConj_sub_id e g]
  set L : V →ₗ[ZMod p] V := (g : V →ₗ[ZMod p] V) - LinearMap.id with hL
  ext w
  simp only [LinearMap.mem_range, Submodule.mem_map, LinearMap.comp_apply]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨L (e.symm u), ⟨e.symm u, rfl⟩, hu⟩
  · rintro ⟨v, ⟨u, hu⟩, hv⟩
    refine ⟨e u, ?_⟩
    rw [show e.symm.toLinearMap (e u) = u by simp, hu, hv]

theorem rxConj_isRefl {p : ℕ} [Fact p.Prime] {V W : Type} [AddCommGroup V] [Module (ZMod p) V]
    [AddCommGroup W] [Module (ZMod p) W] (e : V ≃ₗ[ZMod p] W) (g : V ≃ₗ[ZMod p] V) :
    GGLinRefl (rxConj e g) ↔ GGLinRefl g := by
  unfold GGLinRefl
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have h1' : rxConj e (g * g) = rxConj e 1 := by rw [map_mul, map_one, h1]
      exact (rxConj e).injective h1'
    · rw [rxConj_move e g, LinearEquiv.finrank_map_eq] at h2
      exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [← map_mul, h1, map_one]
    · rw [rxConj_move e g, LinearEquiv.finrank_map_eq]
      exact h2

theorem rxConj_isTransv {p : ℕ} [Fact p.Prime] {V W : Type} [AddCommGroup V] [Module (ZMod p) V]
    [AddCommGroup W] [Module (ZMod p) W] (e : V ≃ₗ[ZMod p] W) (g : V ≃ₗ[ZMod p] V) :
    IsTransv (rxConj e g) ↔ IsTransv g := by
  unfold IsTransv
  have hφ : ∀ u, (rxConj e g) (e u) = e (g u) := by
    intro u
    rw [rxConj_apply]
    simp
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [rxConj_move e g, LinearEquiv.finrank_map_eq] at h1
      exact h1
    · intro v
      have hv := h2 (e v)
      rw [hφ v, ← map_sub, hφ] at hv
      exact e.injective hv
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [rxConj_move e g, LinearEquiv.finrank_map_eq]
      exact h1
    · intro w
      obtain ⟨v, rfl⟩ : ∃ v, w = e v := ⟨e.symm w, by simp⟩
      rw [hφ v, ← map_sub, hφ, h2 v]

theorem ctx_of_conj {P0 : Pt} [Fact P0.p.Prime] {T : Tables} (hp2 : P0.p ≠ 2)
    (hok : verifyAll P0 T = true) {V : Type} [AddCommGroup V] [Module (ZMod P0.p) V]
    (ε : V ≃ₗ[ZMod P0.p] P0.V) (A : Subgroup (V ≃ₗ[ZMod P0.p] V))
    (hfr : ∀ r ∈ P0.gens, ∃ g ∈ A,
      ∀ w : P0.V, ε (g (ε.symm w)) = w - P0.dot (P0.vec r.f) w • P0.vec r.h)
    (hrg : A = Subgroup.closure {s | s ∈ A ∧ GGLinRefl s})
    (hnt : ∀ g ∈ A, ¬ IsTransv g) (hcard : Nat.card A ≤ P0.bound) :
    Ctx P0 T (A.map (rxConj ε).toMonoidHom) := by
  refine ⟨hp2, ?_, ?_, ?_, ?_, hok⟩
  · intro r hr
    obtain ⟨g, hgA, hg⟩ := hfr r hr
    exact ⟨rxConj ε g, Subgroup.mem_map.mpr ⟨g, hgA, rfl⟩, fun w => by
      rw [rxConj_apply]
      exact hg w⟩
  ·
    have himg : {s | s ∈ A.map (rxConj ε).toMonoidHom ∧ GGLinRefl s} =
        (rxConj ε).toMonoidHom '' {s | s ∈ A ∧ GGLinRefl s} := by
      ext s
      constructor
      · rintro ⟨hs, hsr⟩
        obtain ⟨g, hgA, rfl⟩ := Subgroup.mem_map.mp hs
        exact ⟨g, ⟨hgA, (rxConj_isRefl ε g).mp hsr⟩, rfl⟩
      · rintro ⟨g, ⟨hgA, hgr⟩, rfl⟩
        exact ⟨Subgroup.mem_map.mpr ⟨g, hgA, rfl⟩, (rxConj_isRefl ε g).mpr hgr⟩
    rw [himg, ← MonoidHom.map_closure, ← hrg]
  · intro g' hg'
    obtain ⟨g, hgA, rfl⟩ := Subgroup.mem_map.mp hg'
    intro hT
    exact hnt g hgA ((rxConj_isTransv ε g).mp hT)
  · calc Nat.card ↥(A.map (rxConj ε).toMonoidHom) = Nat.card ↥A :=
          (Nat.card_congr (MulEquiv.subgroupMap (rxConj ε) A).toEquiv).symm
      _ ≤ P0.bound := hcard

theorem linWeyl_of_conj {p : ℕ} [Fact p.Prime] {V W : Type} [AddCommGroup V] [Module (ZMod p) V]
    [AddCommGroup W] [Module (ZMod p) W] (ε : V ≃ₗ[ZMod p] W) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (h : ZS.LinWeyl p (A.map (rxConj ε).toMonoidHom)) : ZS.LinWeyl p A := by
  obtain ⟨ι, M, hM, f, hf⟩ := h
  refine ⟨ι, M, hM, f.trans (MulEquiv.subgroupMap (rxConj ε) A).symm, ?_⟩
  intro i
  have hsimple : (((f.trans (MulEquiv.subgroupMap (rxConj ε) A).symm) (M.simple i) : ↥A) :
      V ≃ₗ[ZMod p] V) = (rxConj ε).symm ((f (M.simple i) : W ≃ₗ[ZMod p] W)) := rfl
  rw [hsimple]
  have hrefl : GGLinRefl ((rxConj ε).symm (f (M.simple i) : W ≃ₗ[ZMod p] W)) :=
    (rxConj_isRefl ε.symm _).mpr (hf i)
  exact hrefl

end CFSG.ReflExt

end
