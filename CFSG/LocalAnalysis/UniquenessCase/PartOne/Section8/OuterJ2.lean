module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OuterInnerThree
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.Parity
public import CFSG.Sporadic.Schreier.PairJ2Pairs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Blueprint.NativeSporadic (IsSporadic Carrier)

theorem not_three_dvd_card_outer_of_isSpor_J2
    {X : Type} [Group X] [Finite X]
    (h : IsSporadic X .J2) :
    ¬ 3 ∣ Nat.card (Outer X) := by
  obtain ⟨e⟩ := h
  rw [CFSG.SignalizerFunctorTheorem.CatalogBridge.card_outer_eq_of_mulEquiv e]
  haveI : Finite (Carrier .J2) := Finite.of_equiv X e.toEquiv
  haveI : Finite (MulAut (Carrier .J2)) :=
    Finite.of_injective (fun α : MulAut (Carrier .J2) => (α : Carrier .J2 → Carrier .J2))
      DFunLike.coe_injective
  haveI : Finite (Outer (Carrier .J2)) :=
    Finite.of_surjective (QuotientGroup.mk' (inner (Carrier .J2))) QuotientGroup.mk_surjective
  haveI : Nonempty (Outer (Carrier .J2)) :=
    ⟨QuotientGroup.mk' (inner (Carrier .J2)) 1⟩
  have h2 : Nat.card (Outer (Carrier .J2)) ≤ 2 :=
    CFSG.Sporadic.Schreier.AT_J2_Schreier.1
  intro h3
  have h3le : 3 ≤ Nat.card (Outer (Carrier .J2)) := Nat.le_of_dvd Nat.card_pos h3
  omega

theorem mem_inner_of_isPGroup_three_of_isSpor_J2
    {X : Type} [Group X] [Finite X]
    (h : IsSporadic X .J2) {φ : MulAut X}
    (hφ : IsPGroup 3 (Subgroup.zpowers φ)) :
    φ ∈ inner X :=
  mem_inner_of_isPGroup_three hφ (not_three_dvd_card_outer_of_isSpor_J2 h)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
