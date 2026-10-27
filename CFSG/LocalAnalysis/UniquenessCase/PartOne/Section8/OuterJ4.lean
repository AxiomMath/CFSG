module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.Parity
public import CFSG.RankThree.PartTwo.Sec4.Item47CoreOut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Blueprint.NativeSporadic (IsSporadic Carrier)

theorem not_three_dvd_card_outer_of_isSpor_J4
    {X : Type} [Group X] [Finite X]
    (h : IsSporadic X .J4) :
    ¬ 3 ∣ Nat.card (Outer X) := by
  obtain ⟨e⟩ := h
  rw [CFSG.SignalizerFunctorTheorem.CatalogBridge.card_outer_eq_of_mulEquiv e]
  exact CFSG.RankThree.PartTwo.Sec4.inputs47Core_outJ4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
