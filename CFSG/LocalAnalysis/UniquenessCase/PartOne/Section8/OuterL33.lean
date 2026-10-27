module

public import CFSG.GH74.KGroups.L33
public import CFSG.GH74.E2.K0Simple
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompSpor

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.GH74.KGroups

theorem card_mulAut_le_of_shapeL33
    {K : Type} [Group K]
    (h : CFSG.GH74.E2.ShapeL33 K) :
    Nat.card (MulAut K) ≤ 2 * Nat.card K := by
  obtain ⟨e⟩ := L33.equiv_of_lieModel h
  obtain ⟨M, -, hA⟩ := L33.autModel e
  have hAut : Nat.card (MulAut K) = Nat.card L33.QA.originalSubgroup := by
    rw [M.card_mulAut, hA]
  have hK : Nat.card K = Nat.card L33.QP.originalSubgroup := Nat.card_congr e.toEquiv
  rw [hAut, hK, card_group L33.QA L33.QA_ok, L33.QA_valid.2,
    card_group L33.QP L33.QP_ok, L33.QP_valid.2]

theorem not_three_dvd_card_outer_of_shapeL33
    {K : Type} [Group K] [Finite K]
    (h : CFSG.GH74.E2.ShapeL33 K) :
    ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer K) := by
  haveI : IsSimpleGroup K := (CFSG.GH74.E2.ShapeL33.facts h).1
  refine CFSG.Quasithin.H13.S126C.not_three_dvd_card_outer_of_le ?_ ?_
  · exact CFSG.GH74.E2.center_eq_bot_of_simple_of_not_prime
      (CFSG.GH74.E2.ShapeL33.facts h).2.2
  · exact card_mulAut_le_of_shapeL33 h

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
