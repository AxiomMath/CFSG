module

public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsFull

public section

universe u v w

namespace CFSG.Open

theorem _root_.CFSG.Milestones.cls_connectivity_macwilliams_four_generator
    (S : Type) [Group S] [Finite S] (hS : IsPGroup 2 S)
    (hE : ∀ E : Subgroup S, E.Normal → IsElemAbelian 2 E → Nat.card E ≠ 8) :
    ∀ U : Subgroup S, ∃ X : Finset S, X.card ≤ 4 ∧ Subgroup.closure (X : Set S) = U := by
  exact CFSG.LargeEvenClassification.Helpers.macwilliams_four_generators hS hE

end CFSG.Open
