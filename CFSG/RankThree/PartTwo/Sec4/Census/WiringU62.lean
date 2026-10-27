module

public import CFSG.RankThree.PartTwo.Sec4.Census.Wiring
public import CFSG.RankThree.PartTwo.Census.TripleCoverU62

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

section Item43


theorem rank3II_4_3_of_multipliers_u62 (h41 : Item4_1) (hmult : TripleCoverInputs)
    (hSuz : TripleCoverSuzRankFour) : Item4_3 :=
  rank3II_4_3_of_multipliers h41 hmult hSuz tripleCoverU62RankFour

end Item43

section Item46


theorem rank3II_4_6_of_open_u62 (h41 : Item4_1) (hmult : TripleCoverInputs)
    (hSuz : TripleCoverSuzRankFour) (hsl : CoverSLThree46) (hcen : CoverCenterThree)
    (hu43r : NineCoverU43RankFour) (hrank : RankThree46Open) : Item4_6 :=
  rank3II_4_6_of_open h41 hmult hSuz tripleCoverU62RankFour hsl hcen hu43r hrank

end Item46

end CFSG.RankThree.PartTwo.Sec4.Census
