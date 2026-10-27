module

public import CFSG.LocalAnalysis.StandardType.GGQTwoHeartRoots

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma ggQ2hG_ipair_reindex {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    {M : GGQ2LDatum 3 Bs L x} (D : GGHeartDict M) (a b : M.Λ → ℤ) :
    E6Heart.ipair (fun i => a (D.e i)) (fun i => b (D.e i)) =
      ∑ x, ∑ y, a x * M.cartan x y * b y := by
  unfold E6Heart.ipair
  have hinner : ∀ i : Fin 6,
      (∑ j : Fin 6, a (D.e i) * E6Heart.C i j * b (D.e j)) =
        ∑ y : M.Λ, a (D.e i) * M.cartan (D.e i) y * b y := by
    intro i
    have hC : (∑ j : Fin 6, a (D.e i) * E6Heart.C i j * b (D.e j)) =
        ∑ j : Fin 6, a (D.e i) * M.cartan (D.e i) (D.e j) * b (D.e j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← D.cartan_eq i j]
    rw [hC, Equiv.sum_comp D.e (fun y => a (D.e i) * M.cartan (D.e i) y * b y)]
  rw [Finset.sum_congr rfl (fun i _ => hinner i)]
  exact Equiv.sum_comp D.e (fun x => ∑ y, a x * M.cartan x y * b y)

private def ggQ2hG_vertexEquiv {G : Type} [Group G]
    {Bs L : Subgroup G} {x : G} {M : GGQ2LDatum 3 Bs L x} (D : GGHeartDict M) (yV : M.V) :
    {a : M.Λ → ℤ // CFSG.ClassicalInvolution.RouteD.RRoot M.cartan a ∧
        M.rootForm a yV = 0} ≃ E6Heart.Phi (D.Ψ yV) where
  toFun a := ⟨fun i => a.1 (D.e i), by
    rw [E6Heart.Phi, Finset.mem_filter]
    exact ⟨(GGHeartDict.rootOf_iff D a.1).mp a.2.1, by
      rw [← D.form_eq a.1 yV]
      exact a.2.2⟩⟩
  invFun b := ⟨fun l => b.1 (D.e.symm l), by
    have hb : b.1 ∈ E6Heart.roots ∧ E6Heart.alpha b.1 (D.Ψ yV) = 0 := by
      simpa only [E6Heart.Phi, Finset.mem_filter] using b.2
    constructor
    · rw [GGHeartDict.rootOf_iff D]
      simpa using hb.1
    · rw [D.form_eq]
      simpa using hb.2⟩
  left_inv a := by
    apply Subtype.ext
    funext l
    simp
  right_inv b := by
    apply Subtype.ext
    funext i
    simp

private lemma ggQ2hG_vertexEquiv_apply {G : Type} [Group G]
    {Bs L : Subgroup G} {x : G} {M : GGQ2LDatum 3 Bs L x} (D : GGHeartDict M) (yV : M.V)
    (a : {a : M.Λ → ℤ // CFSG.ClassicalInvolution.RouteD.RRoot M.cartan a ∧
      M.rootForm a yV = 0}) :
    ((ggQ2hG_vertexEquiv D yV a : E6Heart.Phi (D.Ψ yV)) : Fin 6 → ℤ) =
      fun i => a.1 (D.e i) := rfl

private lemma ggQ2hG_graphIso_adj {G : Type} [Group G]
    {Bs L : Subgroup G} {x : G} {M : GGQ2LDatum 3 Bs L x} (D : GGHeartDict M) (yV : M.V)
    (a b : {a : M.Λ → ℤ // CFSG.ClassicalInvolution.RouteD.RRoot M.cartan a ∧
      M.rootForm a yV = 0}) :
    (E6Heart.graph (D.Ψ yV)).Adj (ggQ2hG_vertexEquiv D yV a) (ggQ2hG_vertexEquiv D yV b) ↔
      (M.phiGraph yV).Adj a b := by
  simp only [GGQ2LDatum.phiGraph, E6Heart.graph, SimpleGraph.fromRel_adj,
    ggQ2hG_vertexEquiv_apply]
  rw [ggQ2hG_ipair_reindex D a.1 b.1, ggQ2hG_ipair_reindex D b.1 a.1]
  constructor
  · rintro ⟨hne, hrel⟩
    exact ⟨fun hab => hne (by rw [hab]), hrel⟩
  · rintro ⟨hne, hrel⟩
    exact ⟨fun hab => hne ((ggQ2hG_vertexEquiv D yV).injective hab), hrel⟩

private def ggQ2hG_graphIso {G : Type} [Group G]
    {Bs L : Subgroup G} {x : G} {M : GGQ2LDatum 3 Bs L x} (D : GGHeartDict M) (yV : M.V) :
    M.phiGraph yV ≃g E6Heart.graph (D.Ψ yV) where
  toEquiv := ggQ2hG_vertexEquiv D yV
  map_rel_iff' := fun {a b} => ggQ2hG_graphIso_adj D yV a b

theorem GGHeartDict.comp_transport {G : Type} [Group G]
    {Bs L : Subgroup G} {x : G} {M : GGQ2LDatum 3 Bs L x} (D : GGHeartDict M) (yV : M.V)
    (c : (M.phiGraph yV).ConnectedComponent) :
    ∃ c' : (E6Heart.graph (D.Ψ yV)).ConnectedComponent,
      Nat.card c.supp = E6Heart.compSize (D.Ψ yV) c' ∧
      {v : M.V | ∀ a : c.supp, M.rootForm a.1.1 v = 0} =
        D.Ψ ⁻¹' E6Heart.compKernel (D.Ψ yV) c' := by
  let φ := ggQ2hG_vertexEquiv D yV
  let iso : M.phiGraph yV ≃g E6Heart.graph (D.Ψ yV) := ggQ2hG_graphIso D yV
  refine ⟨SimpleGraph.Iso.connectedComponentEquiv iso c, ?_, ?_⟩
  · show Nat.card c.supp =
      Nat.card (SimpleGraph.Iso.connectedComponentEquiv iso c).supp
    exact Nat.card_congr (SimpleGraph.ConnectedComponent.isoEquivSupp iso c)
  · ext v
    rw [Set.mem_setOf_eq, Set.mem_preimage, E6Heart.compKernel, Set.mem_setOf_eq]
    constructor
    · intro h b hb
      let a : c.supp := (SimpleGraph.ConnectedComponent.isoEquivSupp iso c).symm ⟨b, hb⟩
      have hroot := h a
      rw [D.form_eq a.1.1 v] at hroot
      have ha1 : a.1 = φ.symm b := rfl
      have hval : (φ a.1).1 = b.1 := by
        rw [ha1, Equiv.apply_symm_apply]
      rwa [show (fun i => a.1.1 (D.e i)) = b.1 from by
        rw [← hval]
        rfl] at hroot
    · intro h a
      have hb : ((SimpleGraph.ConnectedComponent.isoEquivSupp iso c) a).1 ∈
          (SimpleGraph.Iso.connectedComponentEquiv iso c).supp :=
        ((SimpleGraph.ConnectedComponent.isoEquivSupp iso c) a).2
      have hthis := h ((SimpleGraph.ConnectedComponent.isoEquivSupp iso c) a).1 hb
      rw [D.form_eq a.1.1 v]
      exact hthis

end CFSG.StandardType

end
