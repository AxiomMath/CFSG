module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryOddMain
public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryChevTwo
public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitarySpor

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem k419UnitaryCensus_holds :
    K419UnitaryCensus :=
  k419UnitaryCensus_of k419UnitaryOddChar_holds k419UnitarySpor_holds k419UnitaryChevTwo_holds

end CFSG.RankThree.PartTwo.Sec4
