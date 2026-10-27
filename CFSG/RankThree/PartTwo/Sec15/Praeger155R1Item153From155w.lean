module

public import CFSG.RankThree.PartTwo.Sec15.Praeger155R1SL25OneOmega
public import CFSG.RankThree.PartTwo.Sec15.F153MainObs8

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec6
  CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec19


theorem item152R_of_155w
    (h155 : Item155wJ2R) (hloc : Claim1411LocalR) (h152b : Item152BigR)
    (h153J2 : Item153MainJ2R) (h149 : Sec16.Item149S14) (h148 : Item148R) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (hSz : KFacts.KPSz) : Item152R :=
  item152R_of_compJ_excl h149 h148 h134 h48 h415 hSz (step152CompJNTR_of_item148R h148)
    (y4CoreExclSL25HJR_of_155w h155 hloc h152b h153J2)

theorem item153MainR_of_155w
    (h155 : Item155wJ2R) (hloc : Claim1411LocalR) (h152b : Item152BigR)
    (h153J2 : Item153MainJ2R) (h316 : Sec19.Item316) (h149 : Sec16.Item149S14) (h148 : Item148R)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (hSz : KFacts.KPSz)
    (h135 : Item135) (h137 : Item137) (h142 : Item142AllS14) (h142c : Sec14.Concl142S14)
    (h143 : Sec14.Concl143S14) (h146 : Sec14.Item146S14) (h1444 : Sec14.Item1444S14)
    (hbot : Sec14.Item145BotS14) (h148HJ : Sec14.Item148HJS14) : Item153MainR :=
  item153MainR_of_twin h149
    (claim153TwinR_of_items h148 h149
      (item152R_of_155w h155 hloc h152b h153J2 h149 h148 h134 h48 h415 hSz))
    (F153.claim153CharR_of_frontier_obs8 h316 h149 h148
      (item152R_of_155w h155 hloc h152b h153J2 h149 h148 h134 h48 h415 hSz)
      h134 h135 h137 h142 h48 h415 h142c h143 h146 h1444 hbot h148HJ)

end CFSG.RankThree.PartTwo.Sec15
