module

public import CFSG.LocalAnalysis.StandardType.GGQTwoAmbModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

@[expose] def GGQTwoAmbBasis {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs : Subgroup G}
    {x y : G} {L H : Subgroup G} (M : GGQTwoAmbModel p Bs x y L H) : Prop :=
  LinearIndependent (ZMod p) M.coroot ∧ Fintype.card M.ι = Module.finrank (ZMod p) M.V

namespace GGQTwoAmbModel

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
  {L H : Subgroup G}

@[expose] noncomputable def parabL (M : GGQTwoAmbModel p Bs x y L H) (S : Set M.ι) :
    Subgroup (M.V ≃ₗ[ZMod p] M.V) :=
  M.toLin.parab S

theorem ggLin_simple (M : GGQTwoAmbModel p Bs x y L H) (k : M.ι) :
    ggLin (p := p) M.model (M.simple k) = M.toLin.simpleRefl k := by
  refine LinearEquiv.ext fun v => ?_
  rw [M.simple_apply]
  exact (Module.reflection_apply v (M.toLin.root_coroot_self k)).symm

theorem parabL_eq_map (M : GGQTwoAmbModel p Bs x y L H) (S : Set M.ι) :
    M.parabL S = (Subgroup.closure (M.simple '' S)).map (ggLin (p := p) M.model) := by
  have himg : ggLin (p := p) M.model '' (M.simple '' S) = M.toLin.simpleRefl '' S := by
    ext t
    constructor
    · rintro ⟨φ, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, (M.ggLin_simple k).symm⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨M.simple k, ⟨k, hk, rfl⟩, M.ggLin_simple k⟩
  rw [show M.parabL S = Subgroup.closure (M.toLin.simpleRefl '' S) from rfl,
    MonoidHom.map_closure, himg]
  rfl

theorem parabL_L (M : GGQTwoAmbModel p Bs x y L H) :
    M.parabL {k | k ≠ M.a} = (ggAutomizer L Bs).map (ggLin (p := p) M.model) := by
  rw [M.parabL_eq_map, ← M.automizer_L]

theorem weyl_le (M : GGQTwoAmbModel p Bs x y L H) :
    M.parabL Set.univ ≤ (ggAutomizer (L ⊔ H) Bs).map (ggLin (p := p) M.model) := by
  rw [M.parabL_eq_map]
  refine Subgroup.map_mono ((Subgroup.closure_le _).mpr ?_)
  rintro t ⟨k, -, rfl⟩
  by_cases hk : k = M.a
  · subst hk
    exact ggAutomizer_mono Bs le_sup_right M.simple_a_mem
  · refine ggAutomizer_mono Bs le_sup_left ?_
    rw [M.automizer_L]
    exact Subgroup.subset_closure ⟨k, hk, rfl⟩

theorem fixed_lin (M : GGQTwoAmbModel p Bs x y L H) (v : M.V) :
    (∀ g ∈ M.parabL {k | k ≠ M.a}, g v = v) ↔ v ∈ Submodule.span (ZMod p) {M.xV} := by
  rw [M.parabL_L, show Submodule.span (ZMod p) {M.xV} =
      ggFixedSubmodule (p := p) M.model (ggAutomizer L Bs) from M.fixed_x.symm,
    mem_ggFixedSubmodule_iff]
  constructor
  · intro h φ hφ
    exact h _ (Subgroup.mem_map.mpr ⟨φ, hφ, rfl⟩)
  · rintro h g hg
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hg
    exact h φ hφ

theorem root_yV (hp : p = 3) (M : GGQTwoAmbModel p Bs x y L H) (k : M.ι) (hka : k ≠ M.a)
    (hkb : k ≠ M.b) : M.root k M.yV = 0 := by
  have h1 : ggLin (p := p) M.model (M.simple k) M.yV = M.yV := by
    rw [GGQTwoAmbModel.yV, ggLin_apply_ofMul, M.y_fixed_J k hka hkb]
  rw [M.simple_apply, sub_eq_self] at h1
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have : CharP (ZMod p) 3 := by
      rw [← hp]
      infer_instance
    exact QTwoLin.two_ne_zero_of_charP_three
  have hc : M.coroot k ≠ 0 := by
    intro h
    apply h2ne
    have h2 := M.toLin.root_coroot_self k
    change M.root k (M.coroot k) = 2 at h2
    rw [← h2, h, map_zero]
  exact (smul_eq_zero.mp h1).resolve_right hc

private lemma model_nsmul (M : GGQTwoAmbModel p Bs x y L H) (n : ℕ) (b : ↥Bs) :
    M.model (n • Additive.ofMul b) = n • M.model (Additive.ofMul b) :=
  (M.model.toAddMonoidHom).map_nsmul n (Additive.ofMul b)

theorem mem_closure_iff (M : GGQTwoAmbModel p Bs x y L H) (d : ↥Bs) :
    (d : G) ∈ Subgroup.closure ({x, y} : Set G) ↔
      M.model (Additive.ofMul d) ∈ Submodule.span (ZMod p) {M.xV, M.yV} := by
  have hmap : Subgroup.map (Subgroup.subtype Bs)
      (Subgroup.closure ({⟨x, M.hx⟩, ⟨y, M.hy⟩} : Set ↥Bs)) =
      Subgroup.closure ({x, y} : Set G) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext g
    constructor
    · rintro ⟨s, hs, hsx⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with hs | hs
      · rw [← hsx, hs]; simp
      · rw [← hsx, hs]; simp
    · intro hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with hg | hg
      · exact ⟨⟨x, M.hx⟩, by simp, hg.symm⟩
      · exact ⟨⟨y, M.hy⟩, by simp, hg.symm⟩
  have hmem : (d : G) ∈ Subgroup.closure ({x, y} : Set G) ↔
      d ∈ Subgroup.closure ({⟨x, M.hx⟩, ⟨y, M.hy⟩} : Set ↥Bs) := by
    rw [← hmap, Subgroup.mem_map]
    constructor
    · rintro ⟨e, he, heq⟩
      have hed : e = d := Subtype.ext heq
      rw [hed] at he
      exact he
    · intro hd
      exact ⟨d, hd, rfl⟩
  rw [hmem]
  constructor
  · intro hd
    refine Subgroup.closure_induction
      (p := fun g _ => M.model (Additive.ofMul g) ∈ Submodule.span (ZMod p) {M.xV, M.yV})
      ?_ ?_ ?_ ?_ hd
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · change M.xV ∈ Submodule.span (ZMod p) {M.xV, M.yV}
        exact Submodule.mem_span_of_mem (by simp)
      · change M.yV ∈ Submodule.span (ZMod p) {M.xV, M.yV}
        exact Submodule.mem_span_of_mem (by simp)
    · rw [show Additive.ofMul (1 : ↥Bs) = 0 from rfl, map_zero]
      exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      rw [ofMul_mul, map_add]
      exact Submodule.add_mem _ ha hb
    · intro a _ ha
      rw [ofMul_inv, map_neg]
      exact Submodule.neg_mem _ ha
  · intro hd
    rw [Submodule.mem_span_pair] at hd
    obtain ⟨c, e, hce⟩ := hd
    have h1 : c • M.xV = M.model (Additive.ofMul ((⟨x, M.hx⟩ : ↥Bs) ^ c.val)) := by
      rw [show M.xV = M.model (Additive.ofMul (⟨x, M.hx⟩ : ↥Bs)) from rfl]
      conv_lhs => rw [← ZMod.natCast_zmod_val c]
      rw [Nat.cast_smul_eq_nsmul, ← M.model_nsmul c.val (⟨x, M.hx⟩ : ↥Bs), ← ofMul_pow]
    have h2 : e • M.yV = M.model (Additive.ofMul ((⟨y, M.hy⟩ : ↥Bs) ^ e.val)) := by
      rw [show M.yV = M.model (Additive.ofMul (⟨y, M.hy⟩ : ↥Bs)) from rfl]
      conv_lhs => rw [← ZMod.natCast_zmod_val e]
      rw [Nat.cast_smul_eq_nsmul, ← M.model_nsmul e.val (⟨y, M.hy⟩ : ↥Bs), ← ofMul_pow]
    have h3 : M.model (Additive.ofMul
        ((⟨x, M.hx⟩ : ↥Bs) ^ c.val * (⟨y, M.hy⟩ : ↥Bs) ^ e.val)) =
        M.model (Additive.ofMul d) := by
      rw [ofMul_mul, map_add, ← h1, ← h2, hce]
    have h4 : (⟨x, M.hx⟩ : ↥Bs) ^ c.val * (⟨y, M.hy⟩ : ↥Bs) ^ e.val = d :=
      Additive.ofMul.injective (M.model.injective h3)
    have hsx : (⟨x, M.hx⟩ : ↥Bs) ∈
        Subgroup.closure ({⟨x, M.hx⟩, ⟨y, M.hy⟩} : Set ↥Bs) :=
      Subgroup.mem_closure_of_mem (by simp)
    have hsy : (⟨y, M.hy⟩ : ↥Bs) ∈
        Subgroup.closure ({⟨x, M.hx⟩, ⟨y, M.hy⟩} : Set ↥Bs) :=
      Subgroup.mem_closure_of_mem (by simp)
    rw [← h4]
    exact Subgroup.mul_mem _ (pow_mem hsx c.val) (pow_mem hsy e.val)

end GGQTwoAmbModel

end CFSG.StandardType

end
