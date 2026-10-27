module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OuterMathieu
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.Parity

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Blueprint.NativeSporadic (IsSporadic Carrier)

theorem not_three_dvd_card_outer_of_isSpor_m12
    {X : Type} [Group X] [Finite X]
    (h : IsSporadic X .M12) :
    ¬ 3 ∣ Nat.card (Outer X) := by
  obtain ⟨e⟩ := h
  rw [CFSG.SignalizerFunctorTheorem.CatalogBridge.card_outer_eq_of_mulEquiv e]
  exact not_three_dvd_card_outer_m12

theorem not_three_dvd_card_outer_of_isSpor_m24
    {X : Type} [Group X] [Finite X]
    (h : IsSporadic X .M24) :
    ¬ 3 ∣ Nat.card (Outer X) := by
  obtain ⟨e⟩ := h
  rw [CFSG.SignalizerFunctorTheorem.CatalogBridge.card_outer_eq_of_mulEquiv e]
  exact not_three_dvd_card_outer_m24

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
