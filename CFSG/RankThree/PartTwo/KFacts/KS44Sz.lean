module

public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
import CFSG.RankThree.PartTwo.KFacts.KS14Sz

public section

namespace CFSG.RankThree.PartTwo.KFacts

theorem kpSz : KPSz := fun S _ _ _ hnab hcat h3 =>
  KS14.suzukiModel_of_inCatalog_of_not_three_dvd S hnab hcat h3

end CFSG.RankThree.PartTwo.KFacts
