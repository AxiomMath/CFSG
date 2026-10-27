module

public import CFSG.Timmesfeld.CorollaryBOutcome
public import CFSG.LargeExtraspecial.S8CorBStatement

public section

namespace CFSG.RankThree.GF2n.Tim77

open Subgroup

@[expose] def CorBFineStatement : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : X), CFSG.Timmesfeld.CorB.Setup t →
    (∃ K : Subgroup X, K ≤ normalClosure ({t} : Set X) ∧
        (K.subgroupOf (normalClosure ({t} : Set X))).Normal ∧ Odd (Nat.card K) ∧
        normalClosure ({t} : Set X) = K ⊔ zpowers t) ∨
      (∀ x ∈ normalClosure ({t} : Set X), ∀ y ∈ normalClosure ({t} : Set X),
        x * y = y * x ∧ x * x = 1) ∨
      (∀ d ∈ CFSG.Timmesfeld.CorB.cls t, ∀ e ∈ CFSG.Timmesfeld.CorB.cls t, orderOf (d * e) ≠ 4) ∨
      ∃ D : Set (↥(normalClosure ({t} : Set X)) ⧸ center ↥(normalClosure ({t} : Set X))),
        CFSG.Timmesfeld.CorB.OutcomeTwo
          (↥(normalClosure ({t} : Set X)) ⧸ center ↥(normalClosure ({t} : Set X))) D

@[expose] def CorBListSimpleStatement : Prop :=
  ∀ (Y : Type) [Group Y], CFSG.LargeExtraspecial.S8.CorBList Y → IsSimpleGroup Y

end CFSG.RankThree.GF2n.Tim77
