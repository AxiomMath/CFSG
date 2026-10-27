module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Defs

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

structure SubgraphProp (T : Track Γ G) (a b : ℤ) (H : Subgroup G) : Prop where
  tarc : IsTArc T a b
  lam : ∃ L ∈ LamSet Γ G (T.line.vert a) (T.line.vert (a + 1)) (T.line.vert (a + 2)), H ≤ L
  stab : ∀ h ∈ H, h • T.line.vert (a + 1) = T.line.vert (a + 1) →
    h • T.line.vert a = T.line.vert a ∨ h • T.line.vert a = T.line.vert (a + 2)
  sub : T.subFixer a b ≤ H
  tau : T.τ ∈ H
  gen : H = Subgroup.closure ((↑(H ⊓ MulAction.stabilizer G (T.line.vert a)) : Set G) ∪
    ↑(H ⊓ MulAction.stabilizer G (T.line.vert (a + 1))))

@[expose] def CommonNbr (Γ : SimpleGraph V) (u u' : V) : Prop :=
  u ≠ u' ∧ ∃ w, Γ.Adj u w ∧ Γ.Adj u' w

@[expose] def IsPartner (Γ : SimpleGraph V) (H : Subgroup G) (u w u' : V) : Prop :=
  u' ∈ MulAction.orbit ↥H u ∧ u' ≠ u ∧ Γ.Adj u' w

theorem mem_orbit_subgroup {H : Subgroup G} {x y : V} :
    y ∈ MulAction.orbit ↥H x ↔ ∃ g ∈ H, g • x = y :=
  ⟨fun ⟨⟨g, hg⟩, h⟩ => ⟨g, hg, h⟩, fun ⟨g, hg, h⟩ => ⟨⟨g, hg⟩, h⟩⟩

theorem CommonNbr.symm {u u' : V} (h : CommonNbr Γ u u') : CommonNbr Γ u' u :=
  ⟨h.1.symm, h.2.imp fun _ hw => ⟨hw.2, hw.1⟩⟩

end CFSG.Quasithin.Fan86
