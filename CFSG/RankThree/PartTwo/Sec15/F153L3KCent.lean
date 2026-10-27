module

public import CFSG.RankThree.PartTwo.Sec15.F153L3KCentSU
public import CFSG.RankThree.PartTwo.Sec15.F153L3KCentLift

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153L3K

theorem kFactL3CentOdd_holds : F153L3C2.KFactL3CentOdd :=
  kFactL3CentOdd_of_s3PartnerFixed fun _ _ _ f hf hT =>
    s3PartnerFixed_of_card (s3CountOK_of_isLThreeEpsAt f hf hT)

end CFSG.RankThree.PartTwo.Sec15.F153L3K
