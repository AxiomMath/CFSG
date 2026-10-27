module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp
public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofSpor

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem noCfgS429_j3 :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .J3) → NoCfgS429 S := by
  intro S _ _ _ hna ⟨e⟩
  haveI : Finite (Blueprint.NativeSporadic.Carrier .J3) := Finite.of_equiv S e.toEquiv
  refine noCfgS429_of_inner (center_eq_bot_of_simple_nonab hna)
    (not_three_dvd_outer_of_mulEquiv e (not_three_dvd_outer_of_le_two card_outer_J3)) ?_
  intro s hs
  have hs' : orderOf (e s) = 3 := by rwa [MulEquiv.orderOf_eq]
  have hc := Sec21.Item228CensusProof.j3ThreeCentralizerCard (e s) hs'
  have hcard := card_centralizer_mulEquiv e s
  rcases hc with h | h
  · exact good429_of_card (B := 11) (hcard.symm.trans h) (by norm_num) (by decide)
  · exact good429_of_card (B := 7) (hcard.symm.trans h) (by norm_num) (by decide)

theorem rowSOf429_j3 :
    RowSOf429 (Spor .J3) :=
  rowSOf429_spor CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv noCfgS429_j3

end CFSG.RankThree.PartTwo.Sec4.RonanK429H
