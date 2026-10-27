module

public import CFSG.RankThree.PartTwo.Sec19.KF1923OutGeneric
import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.A6

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem outTwoExpTwo_alternatingGroup_six :
    OutTwoExpTwo (alternatingGroup (Fin 6)) :=
  outTwoExpTwo_of_forall_sq
    (sq_eq_one_of_outSq CFSG.EvenSporadicStandard.SolomonRed.outSq_alternatingGroup_six)

theorem outTwoAbelian_of_alternatingGroup_six {X : Type} [Group X]
    (e : X ≃* alternatingGroup (Fin 6)) : OutTwoAbelian X :=
  outTwoAbelian_of_mulEquiv e (outTwoAbelian_of_outTwoExpTwo outTwoExpTwo_alternatingGroup_six)

theorem card_outer_dvd_two_of_alternating {X : Type} [Group X] {n : ℕ} (hn : n = 5 ∨ 7 ≤ n)
    (e : X ≃* alternatingGroup (Fin n)) : Nat.card (Outer X) ∣ 2 :=
  CFSG.ComponentClassification.CatalogueSchreierAlternating.outer_card_dvd_two_of_equiv_outside_six
    hn e

theorem outTwoExpTwo_of_tripleA6 {X : Type} [Group X] (hX : Group.IsPerfect X)
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6)) : OutTwoExpTwo X :=
  outTwoExpTwo_of_perfect_quotient hX e outTwoExpTwo_alternatingGroup_six

end CFSG.RankThree.PartTwo.Late
