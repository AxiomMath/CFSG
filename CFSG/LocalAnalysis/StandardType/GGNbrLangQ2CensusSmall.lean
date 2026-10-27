module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusDefs
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1SmallRows
import CFSG.LocalAnalysis.StandardType.GGTwF4SUThreeRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


theorem q2c_rLevel_small :
    Q2CensusRLevel
      (fun lab => lab.tag = .triD4 ∨ lab.tag = .G2 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
        lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der)
      (fun _ => False) := by
  intro p d m lab hp hp2 hΛ hsplit hS hd hm hpd hpm Q hQ
  have hcard : LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
    rcases hS with ht | ht | ht | ht | ht | ht | ht
    · exact TableBExcSmallRest.largeEvenLabelAll_card_lt_triD4
        (fun _ => TableBExcSmallRanks.ggTriD4ThreeRankInput_holds) hp hΛ ht hsplit
    · exact TableBExc.largeEvenLabelAll_card_lt_G2 hp hΛ ht hsplit
    · exact TableBExc.largeEvenLabelAll_card_lt_twB2 hp hΛ ht hsplit
    · exact TableBExcSmallRest.largeEvenLabelAll_card_lt_twF4
        (TableBExcSmallRanks.ggTwF4RankInput_of_three TwF4SUThree.ggTwF4ThreeRankInput_holds)
        hp hΛ ht hsplit
    · obtain rfl := smallDerived_split_three hp hΛ (Or.inl ht) hsplit
      exact ggCSR_B2der hΛ ht
    · obtain rfl := smallDerived_split_three hp hΛ (Or.inr (Or.inl ht)) hsplit
      exact ggCSR_G2der hΛ ht
    · obtain rfl := smallDerived_split_three hp hΛ (Or.inr (Or.inr ht)) hsplit
      exact ggCSR_twF4der hΛ ht
  refine largeEvenRawDatum_mono ?_ (hcard Q hQ)
  rintro R _ I F ⟨hq, hlt⟩
  refine ⟨hq, fun A hA hAI _ h3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ?_⟩
  exact absurd h3 (not_le.2 (hlt A (fun a ha => hAI a ha) hA))

end CFSG.StandardType
