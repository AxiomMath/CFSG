module

public import CFSG.RankThree.PartTwo.Sec18.Item187Min
import CFSG.RankThree.PartTwo.Sec18.Item187Sol

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late

theorem item187_of_cases (h1813 : Item181_3) (h184 : Item184_1) (h186 : Item186H)
    (h5 : ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G) (X : Subgroup G),
      MinCex A M H c X → Group.IsSolvable ↥X → 5 ∣ Nat.card X → False)
    (hn : ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G) (X : Subgroup G),
      MinCex A M H c X → ¬ Group.IsSolvable ↥X → False) : Item187 :=
  item187_of_minCex fun G _ _ A M H c X hX => by
    by_cases hs : Group.IsSolvable ↥X
    · by_cases h5X : 5 ∣ Nat.card X
      · exact h5 G A M H c X hX hs h5X
      · exact hX.false_of_isSolvable_of_not_five_dvd h1813 h184 h186 hs h5X
    · exact hn G A M H c X hX hs

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
