module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.Parity
public import CFSG.Sporadic.Schreier.RuAutInner

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Blueprint.NativeSporadic (IsSporadic Carrier)

theorem not_three_dvd_card_outer_of_isSpor_Ru
    {X : Type} [Group X] [Finite X]
    (h : IsSporadic X .Ru) :
    ¬ 3 ∣ Nat.card (Outer X) := by
  obtain ⟨e⟩ := h
  have hX : Nat.card (Outer X) = Nat.card (Outer (Carrier .Ru)) :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.card_outer_eq_of_mulEquiv e
  have hRu : Nat.card (Outer (Carrier .Ru)) =
      Nat.card (Outer CFSG.Sporadic.RuSchreier.ruP) :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.card_outer_eq_of_mulEquiv
      CFSG.Sporadic.RuSchreier.ruEquivP
  have hP : Nat.card (Outer CFSG.Sporadic.RuSchreier.ruP) = 1 :=
    CFSG.Sporadic.RuSchreier.card_outer_ruP
  rw [hX, hRu, hP]
  norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
