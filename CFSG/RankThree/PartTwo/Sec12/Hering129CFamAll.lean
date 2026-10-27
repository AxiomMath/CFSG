module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CMain
public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam3
public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam4
public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam5
public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam6
public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam7
public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam8

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Hering129C

theorem kFCensus_of_residuals
    (h2 : KFCensus46TwoPi) (h6a : KFCensus46SixL3Pi) (h6b : KFCensus46SixU4)
    (h6c : KFCensus46SixD42) (h6d : KFCensus46SixF4) (h8 : KFCensus46EightChar3) :
    KFCensus :=
  kFCensus_of_families kFCensus46One_holds (kFCensus46Two_of_pi h2) kFCensus46Three_holds
    kFCensus46Four_holds kFCensus46Five_holds (kFCensus46Six_of h6a h6b h6c h6d)
    kFCensus46Seven_holds (kFCensus46Eight_of h8)

theorem gap127TwoCfg_of_residuals
    (h1 : Sec4.Item4_1LargePrime) (h46 : Sec4.Item4_6) (h125 : Item125BarC9)
    (hOTwo : KS129OTwoLie) (h2 : KFCensus46TwoPi) (h6a : KFCensus46SixL3Pi)
    (h6b : KFCensus46SixU4) (h6c : KFCensus46SixD42) (h6d : KFCensus46SixF4)
    (h8 : KFCensus46EightChar3) : Gap127TwoCfg :=
  gap127TwoCfg_of_census h1 h46 h125 hOTwo (kFCensus_of_residuals h2 h6a h6b h6c h6d h8)

end CFSG.RankThree.PartTwo.Sec12
