module

public import CFSG.RankThree.PartTwo.Sec4.Census.WiringNarrow
public import CFSG.RankThree.PartTwo.Census.Sporadic.RankThree46F2
public import CFSG.RankThree.PartTwo.Census.Sporadic.RankThree46Odd

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG.RankThree.PartTwo CFSG.RankThree.PartOne.Census3

theorem rankThree46Sporadic :
    RankThree46Sporadic where
  sporadic s hs _ := by
    simp only [sporadics42not46, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Census.three_le_localRank_of_mem_odd .Ly (by simp)
    · exact Census.three_le_localRank_of_mem_odd .Suz (by simp)
    · exact Census.three_le_localRank_of_mem_odd .ONan (by simp)
    · exact Census.three_le_localRank_of_mem_F2 .Co3 (by simp)
    · exact Census.three_le_localRank_of_mem_F2 .Co2 (by simp)
    · exact Census.three_le_localRank_of_mem_odd .HN (by simp)
    · exact Census.three_le_localRank_of_mem_F2 .Th (by simp)

section Item46


theorem rank3II_4_6_of_cover (h41 : Item4_1) (hmult : TripleCoverInputs)
    (hsl : CoverSLThree46) (hcen : CoverCenterThree) : Item4_6 :=
  rank3II_4_6_of_open_narrow h41 hmult hsl hcen rankThree46Sporadic

end Item46

end CFSG.RankThree.PartTwo.Sec4.Census
