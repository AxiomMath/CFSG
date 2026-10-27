module

public import CFSG.RankThree.PartTwo.Sec19.SimsC198Final
public import CFSG.RankThree.PartTwo.Sec19.SimsC198CaseOneFive
public import CFSG.RankThree.PartTwo.Sec19.SimsC198CaseOdd
public import CFSG.RankThree.PartTwo.Sec19.SimsC198CaseSix
public import CFSG.RankThree.PartTwo.Sec19.SimsC198CaseSeven
public import CFSG.RankThree.PartTwo.Sec19.SimsC198CaseEight

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem SimsC198.mainCensus_holds :
    SimsC198.MainCensus :=
  SimsC198.mainCensus_of_cases SimsC198.caseHolds_one SimsC198.caseHolds_two
    SimsC198.caseHolds_three SimsC198.caseHolds_four SimsC198.caseHolds_five
    SimsC198.caseHolds_six SimsC198.caseHolds_seven SimsC198.caseHolds_eight
    SimsC198.caseHolds_nine

theorem census198_holds :
    Census198 :=
  SimsC198.census198_of_main SimsC198.mainCensus_holds

end CFSG.RankThree.PartTwo.Sec19
