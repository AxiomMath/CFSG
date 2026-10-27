module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartTwo
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartOne

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.RankThree.PartTwo

theorem rank3II_4_4_of (h3 : PrimeThreeLinear) (h2 : PartTwoRankTwo)
    (h3e : PartTwoRankThreeNotQuasisimple) (h3f : PartTwoRankThreeEndgame) : Item4_4 := by
  intro G _ _ hG hperf K _ hK hsimple
  have := hperf
  have := hsimple
  have : (pCore 2 G).Normal := pCore_normal
  by_cases hO2 : pCore 2 G = ⊥
  · by_cases hq : IsQuasisimple G
    · exact Or.inl (LocalCores.isQuasisimple_of_mulEquiv
        ((QuotientGroup.quotientMulEquivOfEq hO2).trans QuotientGroup.quotientBot).symm hq)
    · by_cases h3K : 3 ∣ Nat.card K
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hO2, fun h => absurd h3K h⟩)))
      · rcases rank3II_4_4_partTwo h2 h3e h3f hG hK hO2 h3K hq with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hO2, fun _ => h⟩)))
  · rcases rank3II_4_4_partOne h3 hG hK hO2 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

end CFSG.RankThree.PartTwo.Sec4.Census
