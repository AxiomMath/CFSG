module

public import CFSG.LocalAnalysis.StandardType.GGR4JCardDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def GGR4JCardNC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      GGReflGenerated p (ggAutomizer K Bs) → GGScalarsPmOne Bs → ∀ [Fact p.Prime], p = 3 →
      ∀ (Λ : Type) [Fintype Λ] [DecidableEq Λ] (C : Matrix Λ Λ ℤ) (b c : Λ)
      (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
      (φ' : Option Λ → MulAut ↥Bs) (h' : Option Λ → V) (α' : Option Λ → Module.Dual (ZMod p) V),
      GGExtDatum ι (ggAttachCartan C c) φ' h' α' →
      Submodule.span (ZMod p) (Set.range h') = ⊤ →
      (∃ e : Fin 4 ≃ Λ, ((∀ i j, C (e i) (e j) = CartanMatrix.F₄ i j) ∨
          (∀ i j, C (e i) (e j) = CartanMatrix.F₄ j i)) ∧
        ((b = e 0 ∧ c = e 1) ∨ (b = e 3 ∧ c = e 2))) →
      ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ' (some i)) →
      ggAutomizer K Bs = Subgroup.closure
        ((fun i : Λ => φ' (some i)) '' {i | i ≠ b} ∪ {φ' none}) →
      ((∀ f : ℕ, ¬ GGHasLabel ⟨.C, 3, f⟩ (J ⧸ Subgroup.center J)) →
        48 ≤ Nat.card (ggAutomizer J Bs)) ∧ GGR4JLabel (J ⧸ Subgroup.center J)

end CFSG.StandardType

end
