module

public import CFSG.RankThree.PartTwo.Sec4.Census.WiringU62
public import CFSG.RankThree.PartTwo.Census.NineCoverU43
public import CFSG.RankThree.PartTwo.Census.TripleCoverSuz

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

section Item43


theorem rank3II_4_3_of_multipliers_suz (h41 : Item4_1) (hmult : TripleCoverInputs) : Item4_3 :=
  rank3II_4_3_of_multipliers_u62 h41 hmult tripleCoverSuzRankFour

end Item43

section Item46


theorem rank3II_4_6_of_open_suz (h41 : Item4_1) (hmult : TripleCoverInputs)
    (hsl : CoverSLThree46) (hcen : CoverCenterThree) (hrank : RankThree46Open) : Item4_6 :=
  rank3II_4_6_of_open_u62 h41 hmult tripleCoverSuzRankFour hsl hcen nineCoverU43RankFour hrank

end Item46

end CFSG.RankThree.PartTwo.Sec4.Census
