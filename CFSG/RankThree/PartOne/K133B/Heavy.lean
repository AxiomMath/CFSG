module

public import CFSG.RankThree.PartOne.K133B.Pair2
public import CFSG.RankThree.PartOne.K133B.Items1
public import CFSG.RankThree.PartOne.K133B.Items2
public import CFSG.RankThree.PartOne.K133B.Items3
public import CFSG.RankThree.PartOne.K133B.Items4

public section

namespace CFSG.RankThree.PartOne.K133B

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K133
  CFSG.RankThree.PartOne.Q1327T

@[expose] def Row8OddHeavy : Prop :=
  Row8OddAt (K133.leaf4 0) ∧ Row8OddAt (K133.leaf7 5) ∧ Row8OddAt (K133.leaf7 8) ∧
    Row8OddAt (K133.leaf7 9) ∧ Row8NotCentral5

section Assembly

theorem row8OddItem_three (h0 : Row8OddAt (K133.leaf4 0)) : Row8OddItem 3 :=
  Row8OddAt.of_exists (Q := K133.leaf4) (fun X _ hX => by
    obtain ⟨q, hq, he, h0 | h1 | h2 | h3⟩ := hX
    · exact ⟨0, q, hq, he, h0⟩
    · exact ⟨1, q, hq, he, h1⟩
    · exact ⟨2, q, hq, he, h2⟩
    · exact ⟨3, q, hq, he, h3⟩) (fun i => by
    fin_cases i
    · exact h0
    · exact row8OddAt_leaf4_one
    · exact row8OddAt_leaf4_two
    · exact row8OddAt_leaf4_three)

theorem row8OddItem_seven : Row8OddItem 7 :=
  Row8OddAt.of_exists (Q := K133.leaf8) (fun X _ hX => by
    obtain ⟨q, hq, h0 | h1 | h2⟩ := hX
    · exact ⟨0, q, hq, h0⟩
    · exact ⟨1, q, hq, h1⟩
    · exact ⟨2, q, hq, h2⟩) (fun i => by
    fin_cases i
    · exact row8OddAt_leaf8_zero
    · exact row8OddAt_leaf8_one
    · exact row8OddAt_leaf8_two)

end Assembly

section Six

theorem row8OddItem_six (h5 : Row8OddAt (K133.leaf7 5)) (h8 : Row8OddAt (K133.leaf7 8))
    (h9 : Row8OddAt (K133.leaf7 9)) : Row8OddItem 6 :=
  Row8OddAt.of_exists (Q := K133.leaf7) (fun X _ hX => by
    rcases hX with ⟨q, hq, h⟩ | ⟨m, h⟩ | ⟨q, hq, h | h | h | h | h | h | h⟩ | ⟨m, h⟩ | h
    · exact ⟨0, q, hq, h⟩
    · exact ⟨1, m, h⟩
    · exact ⟨2, q, hq, h⟩
    · exact ⟨3, q, hq, h⟩
    · exact ⟨4, q, hq, h⟩
    · exact ⟨5, q, hq, h⟩
    · exact ⟨6, q, hq, h⟩
    · exact ⟨7, q, hq, h⟩
    · exact ⟨8, q, hq, h⟩
    · exact ⟨9, m, h⟩
    · exact ⟨10, h⟩) (fun i => by
    fin_cases i
    · exact row8OddAt_leaf7_zero
    · exact row8OddAt_leaf7_one
    · exact row8OddAt_leaf7_two
    · exact row8OddAt_leaf7_three
    · exact row8OddAt_leaf7_four
    · exact h5
    · exact row8OddAt_leaf7_six
    · exact row8OddAt_leaf7_seven
    · exact h8
    · exact h9
    · exact row8OddAt_leaf7_ten)

end Six

section Eight

theorem row8OddItem_eight : Row8OddItem 8 :=
  Row8OddAt.of_exists (Q := K133.leaf9) (fun X _ hX => by
    obtain ⟨q, hq, he, h0 | h1 | h2 | h3 | h4 | h5 | h6⟩ := hX
    · exact ⟨0, q, hq, he, h0⟩
    · exact ⟨1, q, hq, he, h1⟩
    · exact ⟨2, q, hq, he, h2⟩
    · exact ⟨3, q, hq, he, h3⟩
    · exact ⟨4, q, hq, he, h4⟩
    · exact ⟨5, q, hq, he, h5⟩
    · exact ⟨6, q, hq, he, h6⟩) (fun i => by
    fin_cases i
    · exact row8OddAt_leaf9_zero
    · exact row8OddAt_leaf9_one
    · exact row8OddAt_leaf9_two
    · exact row8OddAt_leaf9_three
    · exact row8OddAt_leaf9_four
    · exact row8OddAt_leaf9_five
    · exact row8OddAt_leaf9_six)

end Eight

section Final

theorem row8OddInspection_of_heavy (hH : Row8OddHeavy) : Row8OddInspection :=
  row8Odd_of_items fun i => by
    fin_cases i
    · exact row8OddItem_zero
    · exact row8OddItem_one
    · exact row8OddItem_two
    · exact row8OddItem_three hH.1
    · exact row8OddItem_four
    · exact row8OddItem_five
    · exact row8OddItem_six hH.2.1 hH.2.2.1 hH.2.2.2.1
    · exact row8OddItem_seven
    · exact row8OddItem_eight

end Final

end CFSG.RankThree.PartOne.K133B
