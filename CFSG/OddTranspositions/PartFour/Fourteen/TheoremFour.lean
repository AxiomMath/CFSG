module

public import CFSG.OddTranspositions.PartFour.Fourteen.Statements
public import CFSG.OddTranspositions.PartFour.Statements

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Bridge.OddTransp

@[expose] def Theorem4List : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D),
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) → HypothesisE hC →
    CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha) →
    AscList G D

end CFSG.OddTranspositions.PartFour
