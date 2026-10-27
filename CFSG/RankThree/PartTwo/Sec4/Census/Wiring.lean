module

public import CFSG.RankThree.PartTwo.Sec4.Census.WiringInputs
public import CFSG.RankThree.PartTwo.Sec4.Census.Assembly4
public import CFSG.RankThree.PartOne.CTP.SpinRankFour
public import CFSG.RankThree.PartOne.CTP.BabyRankFour
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG.RankThree.PartTwo CFSG.RankThree.PartOne.Census3
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

section Item42

theorem rank3II_4_2 : Item4_2 :=
  rank3II_4_2_of_open PartOne.CTP.spinRankFour PartOne.CTP.rankFourBabyMonster
    PartTwo.Census.bridgeSp6Two PartTwo.Census.bridgeSp6Four PartTwo.Census.bridgeSp8Two
    PartTwo.Census.bridgeOmega8PlusTwo PartTwo.Census.bridgeOmega8MinusTwo
    spinLargePrimeRankThree

end Item42

section Item43

theorem rank3II_4_3_of_multipliers (h41 : Item4_1) (hmult : TripleCoverInputs)
    (hSuz : TripleCoverSuzRankFour) (hU62 : TripleCoverU62RankFour) : Item4_3 :=
  rank3II_4_3_of_inputs h41 hmult hSuz hU62 PartOne.CTP.spinRankFour

end Item43

section Item46

theorem rank3II_4_6_of_open (h41 : Item4_1) (hmult : TripleCoverInputs)
    (hSuz : TripleCoverSuzRankFour) (hU62 : TripleCoverU62RankFour) (hsl : CoverSLThree46)
    (hcen : CoverCenterThree) (hu43r : NineCoverU43RankFour) (hrank : RankThree46Open) :
    Item4_6 :=
  rank3II_4_6_of h41 rank3II_4_2 (rank3II_4_3_of_multipliers h41 hmult hSuz hU62)
    (Inputs46.of_open hsl hcen hu43r hrank)

end Item46

section Census44

theorem twoCoverCensus_of_open (hGA : GriessMultipliersAllModels)
    (hSpor : SporadicMultipliers) (hcov : TwoCoverRanksOpen) : TwoCoverCensus :=
  twoCoverCensus_of rank3II_4_2 hGA griessMultipliersCentralCovers hSpor
    (TwoCoverRanks.of_open hcov)

theorem quasisimpleCensus_of_open (h41 : Item4_1) (hGA : GriessMultipliersAllModels)
    (hSpor : SporadicMultipliers) (hcov : TwoCoverRanksOpen) : QuasisimpleCensus :=
  quasisimpleCensus_of_inputs h41 rank3II_4_2 hGA griessMultipliersCentralCovers hSpor
    (TwoCoverRanks.of_open hcov)

end Census44

section Item44

theorem rank3II_4_4_of_open (h41 : Item4_1) (hGA : GriessMultipliersAllModels)
    (hSpor : SporadicMultipliers) (hcov : TwoCoverRanksOpen) (hL34 : FourL34NotSLFourOdd) :
    Item4_4 :=
  rank3II_4_4_of_inputs h41 rank3II_4_2 hGA griessMultipliersCentralCovers hSpor
    (TwoCoverRanks.of_open hcov) hL34

end Item44

end CFSG.RankThree.PartTwo.Sec4.Census
