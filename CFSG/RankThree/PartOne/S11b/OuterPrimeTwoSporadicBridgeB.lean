module

public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadic
import CFSG.Sporadic.Schreier.PairMcLOut
import CFSG.Sporadic.Schreier.J4SOuter
import CFSG.Sporadic.Schreier.RuAutInner
import CFSG.Sporadic.FischerOddCore.Fi23Aut
import CFSG.LocalAnalysis.ComponentClassification.CatalogueOuterTwoPartSporadicCases
public import CFSG.Sporadic.Schreier.RuDefs

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

namespace OuterPrimeTwoBridge

theorem card_outer_eq {T T' : Type*} [Group T] [Group T'] (e : T ≃* T') :
    Nat.card (Outer T) = Nat.card (Outer T') :=
  Nat.card_congr (equivalence e).toEquiv

end OuterPrimeTwoBridge

theorem sporadicOuterSmall_McL : SporadicOuterSmall .McL :=
  Or.inl (lt_of_le_of_lt Sporadic.Schreier.McL_outer_card_le_two.1 (by norm_num))

theorem sporadicOuterSmall_He : SporadicOuterSmall .He :=
  Or.inl (lt_of_le_of_lt Sporadic.Schreier.AT_He_Schreier.1 (by norm_num))

theorem sporadicOuterSmall_Fi22 : SporadicOuterSmall .Fi22 :=
  Or.inl (lt_of_le_of_lt
    (ComponentClassification.CatalogueOuterTwoPart.card_outer_fi22.le) (by norm_num))

theorem sporadicOuterSmall_Fi23 : SporadicOuterSmall .Fi23 :=
  Or.inl (lt_of_le_of_lt Sporadic.FischerOddCore.card_outer_fi23.le (by norm_num))

theorem sporadicOuterSmall_Fi24Prime : SporadicOuterSmall .Fi24Prime :=
  Or.inl (lt_of_le_of_lt Sporadic.Schreier.Fi24.card_outer_fi24prime.le (by norm_num))

theorem sporadicOuterSmall_Ru : SporadicOuterSmall .Ru := by
  refine Or.inl ?_
  rw [show Nat.card (Outer (NativeSporadic.Carrier .Ru)) =
      Nat.card (Outer Sporadic.RuSchreier.ruP) from
    OuterPrimeTwoBridge.card_outer_eq Sporadic.RuSchreier.ruEquivP,
    Sporadic.RuSchreier.card_outer_ruP]
  norm_num

theorem sporadicOuterSmall_J4 : SporadicOuterSmall .J4 := by
  right
  intro q hq hq5 hdvd
  have hJ4 : Nonempty (NativeSporadic.Carrier .J4 ≃* NativeSporadic.J4) := ⟨MulEquiv.refl _⟩
  rcases (Sporadic.J4Schreier.R3E_J4_outer_automorphism_group_no_large_primes
    (T := NativeSporadic.Carrier .J4) hJ4).1 q hq hdvd with rfl | rfl <;> omega

end CFSG.RankThree.PartOne
