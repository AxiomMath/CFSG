module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4SubDefs

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {T : Track Γ G}
  {a b : ℤ} {H : Subgroup G}

@[expose] def OrbitAdj (Γ : SimpleGraph V) (A : Set V) (u u' : V) : Prop :=
  u ∈ A ∧ u' ∈ A ∧ CommonNbr Γ u u'

theorem OrbitAdj.symm {A : Set V} {u u' : V} (h : OrbitAdj Γ A u u') : OrbitAdj Γ A u' u :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

theorem orbitAdj_smul (F : FanTree Γ G) {h : G} (hh : h ∈ H) {u u' : V}
    (hu : OrbitAdj Γ (MulAction.orbit ↥H (T.line.vert a)) u u') :
    OrbitAdj Γ (MulAction.orbit ↥H (T.line.vert a)) (h • u) (h • u') := by
  obtain ⟨hA, hA', hne, w, hw, hw'⟩ := hu
  have hmem : ∀ {v : V}, v ∈ MulAction.orbit ↥H (T.line.vert a) →
      h • v ∈ MulAction.orbit ↥H (T.line.vert a) := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := mem_orbit_subgroup.1 hv
    exact mem_orbit_subgroup.2 ⟨h * k, H.mul_mem hh hk, by rw [mul_smul]⟩
  exact ⟨hmem hA, hmem hA', fun e => hne (MulAction.injective h e), h • w,
    (F.adj_smul h _ _).2 hw, (F.adj_smul h _ _).2 hw'⟩

theorem OrbitAdj.reflTransGen_symm {A : Set V} {u v : V}
    (h : Relation.ReflTransGen (OrbitAdj Γ A) u v) : Relation.ReflTransGen (OrbitAdj Γ A) v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head hbc.symm ih

theorem reflTransGen_orbitAdj_smul (F : FanTree Γ G) {h : G} (hh : h ∈ H) {u v : V}
    (hr : Relation.ReflTransGen (OrbitAdj Γ (MulAction.orbit ↥H (T.line.vert a))) u v) :
    Relation.ReflTransGen (OrbitAdj Γ (MulAction.orbit ↥H (T.line.vert a))) (h • u) (h • v) := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (orbitAdj_smul F hh hbc)

namespace SubgraphProp

theorem comp_invariant (F : FanTree Γ G) {h : G} (hh : h ∈ H)
    (hx : Relation.ReflTransGen (OrbitAdj Γ (MulAction.orbit ↥H (T.line.vert a)))
      (T.line.vert a) (h • T.line.vert a)) (u : V) :
    Relation.ReflTransGen (OrbitAdj Γ (MulAction.orbit ↥H (T.line.vert a))) (T.line.vert a) u ↔
      Relation.ReflTransGen (OrbitAdj Γ (MulAction.orbit ↥H (T.line.vert a)))
        (T.line.vert a) (h • u) := by
  constructor
  · intro hu
    exact hx.trans (reflTransGen_orbitAdj_smul F hh hu)
  · intro hu
    have h1 := reflTransGen_orbitAdj_smul (T := T) (a := a) F (H.inv_mem hh) hu
    have h2 := reflTransGen_orbitAdj_smul (T := T) (a := a) F (H.inv_mem hh) hx
    rw [inv_smul_smul] at h1 h2
    exact (OrbitAdj.reflTransGen_symm h2).trans h1

theorem orbit_chain (hS : SubgraphProp T a b H) (F : FanTree Γ G) {u : V}
    (hu : u ∈ MulAction.orbit ↥H (T.line.vert a)) :
    Relation.ReflTransGen (OrbitAdj Γ (MulAction.orbit ↥H (T.line.vert a))) (T.line.vert a) u := by
  obtain ⟨h, hh, rfl⟩ := mem_orbit_subgroup.1 hu
  have hα : T.line.vert a ∈ MulAction.orbit ↥H (T.line.vert a) := MulAction.mem_orbit_self _
  have hα₂ : T.line.vert (a + 2) ∈ MulAction.orbit ↥H (T.line.vert a) :=
    mem_orbit_subgroup.2 ⟨T.τ, hS.tau, T.trans a⟩
  have hadj : OrbitAdj Γ (MulAction.orbit ↥H (T.line.vert a)) (T.line.vert a)
      (T.line.vert (a + 2)) := by
    refine ⟨hα, hα₂, T.line.nb a, T.line.vert (a + 1), T.line.adj a, ?_⟩
    have := (T.line.adj (a + 1)).symm
    rwa [show a + 1 + 1 = a + 2 by omega] at this
  have hgen : h ∈ Subgroup.closure ((↑(H ⊓ MulAction.stabilizer G (T.line.vert a)) : Set G) ∪
      ↑(H ⊓ MulAction.stabilizer G (T.line.vert (a + 1)))) := hS.gen ▸ hh
  have key : ∀ g ∈ Subgroup.closure ((↑(H ⊓ MulAction.stabilizer G (T.line.vert a)) : Set G) ∪
      ↑(H ⊓ MulAction.stabilizer G (T.line.vert (a + 1)))), ∀ u : V,
      (Relation.ReflTransGen (OrbitAdj Γ (MulAction.orbit ↥H (T.line.vert a))) (T.line.vert a) u ↔
        Relation.ReflTransGen (OrbitAdj Γ (MulAction.orbit ↥H (T.line.vert a)))
          (T.line.vert a) (g • u)) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · refine comp_invariant F hx.1 ?_
        rw [MulAction.mem_stabilizer_iff.1 hx.2]
      · refine comp_invariant F hx.1 ?_
        rcases hS.stab x hx.1 (MulAction.mem_stabilizer_iff.1 hx.2) with h | h
        · rw [h]
        · rw [h]
          exact Relation.ReflTransGen.single hadj
    | one => simp
    | mul x y _ _ hx hy =>
      intro u
      rw [hy u, hx (y • u), mul_smul]
    | inv x _ hx =>
      intro u
      rw [hx (x⁻¹ • u), smul_inv_smul]
  have := (key h hgen (T.line.vert a)).1 Relation.ReflTransGen.refl
  exact this

end SubgraphProp

theorem fan46_conn (hS : SubgraphProp T a b H) (F : FanTree Γ G) {S : Set V}
    (hSA : S ⊆ MulAction.orbit ↥H (T.line.vert a)) (hne : S.Nonempty)
    (hcl : ∀ u ∈ S, ∀ u' ∈ MulAction.orbit ↥H (T.line.vert a), CommonNbr Γ u' u → u' ∈ S) :
    S = MulAction.orbit ↥H (T.line.vert a) := by
  obtain ⟨u₀, hu₀⟩ := hne
  have hchain : ∀ v : V, Relation.ReflTransGen
      (OrbitAdj Γ (MulAction.orbit ↥H (T.line.vert a))) u₀ v → v ∈ S := by
    intro v hv
    induction hv with
    | refl => exact hu₀
    | tail _ hbc ih => exact hcl _ ih _ hbc.2.1 hbc.2.2.symm
  refine Set.Subset.antisymm hSA fun u hu => hchain u ?_
  exact (OrbitAdj.reflTransGen_symm (hS.orbit_chain F (hSA hu₀))).trans (hS.orbit_chain F hu)

end CFSG.Quasithin.Fan86
