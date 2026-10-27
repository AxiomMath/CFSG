module

public import CFSG.Milestones.CLS_connectivity_MacWilliams_four_generator

public section

universe u v w

namespace CFSG.Open.Open

theorem macwilliams_four_generator
    (S : Type) [Group S] [Finite S] (hS : IsPGroup 2 S)
    (hE : ∀ E : Subgroup S, E.Normal → IsElemAbelian 2 E → Nat.card E ≠ 8) :
    ∀ U : Subgroup S, ∃ X : Finset S, X.card ≤ 4 ∧ Subgroup.closure (X : Set S) = U :=
  _root_.CFSG.Milestones.cls_connectivity_macwilliams_four_generator S hS hE

end CFSG.Open.Open
