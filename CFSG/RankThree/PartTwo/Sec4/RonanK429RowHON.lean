module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp
public import CFSG.RankThree.PartTwo.KFacts.K426RestON

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem noCfgS429_on :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .ONan) → NoCfgS429 S := by
  intro S _ _ _ hna ⟨e⟩
  haveI : Finite (Blueprint.NativeSporadic.Carrier .ONan) := Finite.of_equiv S e.toEquiv
  refine noCfgS429_of_inner (center_eq_bot_of_simple_nonab hna)
    (not_three_dvd_outer_of_mulEquiv e inputs47Core_outON) ?_
  intro s hs
  have hs' : orderOf (e s) = 3 := by rwa [MulEquiv.orderOf_eq]
  have hc := K426Rest.onThreeCentralizer (e s) hs'
  have hcard := card_centralizer_mulEquiv e s
  exact good429_of_card (B := 15) (hcard.symm.trans hc) (by norm_num) (by decide)

theorem rowSOf429_on :
    RowSOf429 (Spor .ONan) :=
  rowSOf429_spor CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv noCfgS429_on

end CFSG.RankThree.PartTwo.Sec4.RonanK429H
