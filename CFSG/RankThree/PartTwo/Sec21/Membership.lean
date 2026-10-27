module

public import CFSG.RankThree.PartTwo.Sec21.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type*} [Group G]

theorem mem_lThreeStar_of_mem_lThreeStarPairs {A E U L : Subgroup G} {c : G}
    (hE : E ∈ collectionIn (partTwoE G) A) (hU : U ∈ fourGroups E)
    (h : (c, L) ∈ lThreeStarPairs A E U) : L ∈ lThreeStar A :=
  ⟨mem_lZeroStar_of_mem_lThreeStarPairs h, E, hE, U, hU, c, h⟩

theorem mem_lThreeStarAt_of_mem_lThreeStarPairs {A E U L : Subgroup G} {c : G}
    (hE : E ∈ collectionIn (partTwoE G) A) (hU : U ∈ fourGroups E)
    (h : (c, L) ∈ lThreeStarPairs A E U) : L ∈ lThreeStarAt A c :=
  ⟨mem_lThreeStar_of_mem_lThreeStarPairs hE hU h, (lZeroStarAt_subset A c) h.2.2.1⟩

theorem Sec21Pair.mem_lThreeStarAt {G : Type} [Group G] [Finite G] {A E U L : Subgroup G}
    {c : G} (h : Sec21Pair G A E U c L) : L ∈ lThreeStar A ∧ L ∈ lThreeStarAt A c :=
  ⟨mem_lThreeStar_of_mem_lThreeStarPairs h.mem_E h.mem_U h.mem_pair,
    mem_lThreeStarAt_of_mem_lThreeStarPairs h.mem_E h.mem_U h.mem_pair⟩

end CFSG.RankThree.PartTwo.Sec21
