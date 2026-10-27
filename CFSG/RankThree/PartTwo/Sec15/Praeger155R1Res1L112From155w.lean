module

public import CFSG.RankThree.PartTwo.Sec15.Praeger155R1Item153From155w
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Omega

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec6
  CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec19
  CFSG.RankThree.PartTwo.Sec15.Sylow155R1

theorem claim153ObsR_of_155w
    (h155 : Item155wJ2R) (hloc : Claim1411LocalR) (h152b : Item152BigR)
    (h153J2 : Item153MainJ2R) (h316 : Sec19.Item316) (h149 : Sec16.Item149S14) (h148 : Item148R)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (hSz : KFacts.KPSz) :
    Claim153ObsR :=
  F153Obs.claim153ObsR_of F153Obs.theoremA881
    (claim153TwinTypes_of h148 h149
      (item152R_of_155w h155 hloc h152b h153J2 h149 h148 h134 h48 h415 hSz)
      (claim153TwinCase7_of_item148R h148))
    h149 (item152R_of_155w h155 hloc h152b h153J2 h149 h148 h134 h48 h415 hSz)

end CFSG.RankThree.PartTwo.Sec15
