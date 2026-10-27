module

public import CFSG.RankThree.PartOne.Q1327T.Item1PSL2
public import CFSG.RankThree.PartOne.Q1327T.Item2L3U3
public import CFSG.RankThree.PartOne.Q1327T.Item3Ree
public import CFSG.RankThree.PartOne.Q1327T.Item5Alt
public import CFSG.RankThree.PartOne.Q1327S.Main
public import CFSG.RankThree.PartOne.Q1327F.Main
public import CFSG.RankThree.PartOne.Q1327T.Item7Rank1
public import CFSG.RankThree.PartOne.Q1327T.Item7L3
public import CFSG.RankThree.PartOne.Q1327T.Item7Sp4
public import CFSG.RankThree.PartOne.Q1327T.Item7U4
public import CFSG.RankThree.PartOne.Q1327T.Item7U5Five
public import CFSG.RankThree.PartOne.Q1327T.Item7Tits
public import CFSG.RankThree.PartOne.Q1327T.Item7D4
public import CFSG.RankThree.PartOne.Q1327T.Item7F4
public import CFSG.RankThree.PartOne.Q1327T.R8F4
public import CFSG.RankThree.PartOne.Q1327T.R8Item9

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K133

section ItemSix

theorem row8U3Item_six_of_leaves
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    Row8U3Item 6 :=
  Row8U3At.of_exists (Q := K133.leaf7) (fun X _ hX => by
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
    · exact row8U3At_leaf7_zero
    · exact row8U3At_leaf7_one
    · exact row8U3At_leaf7_two hGA
    · exact row8U3At_leaf7_three hGA
    · exact row8U3At_leaf7_four hGA
    · exact row8U3At_leaf7_five hGA
    · exact row8U3At_leaf7_six hGA
    · exact row8U3At_leaf7_seven hGA
    · exact row8U3At_leaf7_eight hGA
    · exact row8U3At_leaf7_nine hGA
    · exact row8U3At_leaf7_ten hGA)

end ItemSix

section Final

theorem row8U3Inspection_of_leaves
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    Row8U3Inspection :=
  row8U3_of_items fun i => by
    fin_cases i
    · exact row8U3Item_zero
    · exact row8U3Item_one
    · exact row8U3Item_two
    · exact Q1327F.row8U3Item_three hGA
    · exact row8U3Item_four
    · exact Q1327S.row8U3Item_sporadic
    · exact row8U3Item_six_of_leaves hGA
    · exact row8U3Item_seven hGA
    · exact row8U3Item_nine hGA (row8U3At_leaf9_six hGA)

end Final

end CFSG.RankThree.PartOne.Q1327T
