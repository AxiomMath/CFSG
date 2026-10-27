module

public import CFSG.RankThree.PartTwo.Sec4.Census.WiringSuz
public import CFSG.RankThree.PartTwo.Sec4.Census.RankOmegaF4

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG.RankThree.PartTwo CFSG.RankThree.PartOne.Census3
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

section Item46


theorem rank3II_4_6_of_open_narrow (h41 : Item4_1) (hmult : TripleCoverInputs)
    (hsl : CoverSLThree46) (hcen : CoverCenterThree) (hrank : RankThree46Sporadic) : Item4_6 :=
  rank3II_4_6_of_open_suz h41 hmult hsl hcen (RankThree46Open.of_sporadic hrank)

end Item46

section Census44


theorem quasisimpleCensus_of_open_narrow (h41 : Item4_1) (hGA : GriessMultipliersAllModels)
    (hSpor : SporadicMultipliers) (hcov : TwoCoverRanksOpen') : QuasisimpleCensus :=
  quasisimpleCensus_of_open h41 hGA hSpor (TwoCoverRanksOpen.of_open' hcov)

end Census44

section Item44


theorem rank3II_4_4_of_open_narrow (h41 : Item4_1) (hGA : GriessMultipliersAllModels)
    (hSpor : SporadicMultipliers) (hcov : TwoCoverRanksOpen') (hL34 : FourL34NotSLFourOdd) :
    Item4_4 :=
  rank3II_4_4_of_open h41 hGA hSpor (TwoCoverRanksOpen.of_open' hcov) hL34

end Item44

end CFSG.RankThree.PartTwo.Sec4.Census
