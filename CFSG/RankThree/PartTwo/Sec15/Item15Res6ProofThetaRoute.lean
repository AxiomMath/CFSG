module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res6ProofTheta
public import CFSG.RankThree.PartTwo.Sec16.Item162Res5ProofPoint
public import CFSG.RankThree.PartTwo.Sec16.Item162Res5ProofFaithful
public import CFSG.RankThree.PartTwo.Sec16.Item162Res6ProofA7
public import CFSG.RankThree.PartTwo.Sec16.Item162Res7ProofTwoInner
public import CFSG.RankThree.PartTwo.Sec16.Item162Res7ProofNormSolv
public import CFSG.RankThree.PartTwo.Sec16.Item162Res7ProofOdd

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

theorem item162R_of_res5_core
    (h1514 : Item1514R) (h1523 : Item1523R) (h153 : Item153MainR) (hobs : Claim153ObsR)
    (hn : Claim153NormalR) (h1411 : Item1411_1R) (h155 : Item155R)
    (hWloc : Claim1411NonsolvWR) (h1444 : Item1444S14) (h146 : Item146S14)
    (hbot : Item145BotS14) (h142 : Concl142S14) (hU35 : Step163U35)
    (hRead : Y4CoreReadR) (hMem : Y4CoreMemR) (h148 : Item148SmallS14) (hCore : Step148Core)
    (hPoint : Step148Point) (hKT : Step148KType) (h135 : Item135) (hOdd : Step162UJOdd)
    (hHJ : Step162UJHJSimple) (hFree : Step162A7OtherFree) : Item162R :=
  item162R_of_res4C_core h1514 h1523 h153 hobs hn h1411 h155 hWloc h1444 h146 hbot h142 hU35
    (step163MeetsPoint_of_steps148 hCore hPoint hKT) hRead hMem h148 hOdd hHJ
    (step162LPointA7_of_items hCore hPoint hKT h135 (concl142R_of_S14 h142))
    (step162ChoiceFaithful_of (concl142R_of_S14 h142))
    (step162A7OtherSevenC_of_free h155 h153 hWloc (concl142R_of_S14 h142) hFree)

theorem item162R_of_res6_core
    (h1514 : Item1514R) (h1523 : Item1523R) (h153 : Item153MainR) (hobs : Claim153ObsR)
    (hn : Claim153NormalR) (h1411 : Item1411_1R) (h155 : Item155R)
    (hWloc : Claim1411NonsolvWR) (h1444 : Item1444S14) (h146 : Item146S14)
    (hbot : Item145BotS14) (h142 : Concl142S14) (hU35 : Step163U35)
    (hRead : Y4CoreReadR) (hMem : Y4CoreMemR) (h148 : Item148SmallS14) (hCore : Step148Core)
    (hPoint : Step148Point) (hKT : Step148KType) (h135 : Item135)
    (hOdd : Step162UJOddProper) (hK : KS162J2TwoInner) (hNS2 : KS162J2NormSolv)
    (hFree : Step162A7OtherFreeMeet) : Item162R :=
  item162R_of_res5_core h1514 h1523 h153 hobs hn h1411 h155 hWloc h1444 h146 hbot h142 hU35
    hRead hMem h148 hCore hPoint hKT h135 (step162UJOdd_of_proper h155 hOdd)
    (step162UJHJSimple_of_kfacts h155 h153 h1444 h146 hbot h142 h1523 hK hNS2)
    (step162A7OtherFree_of_meet h155 h153 hWloc h1444 h146 hbot h142 hFree)

theorem item162R_of_res7_core
    (h1514 : Item1514R) (h1523 : Item1523R) (h153 : Item153MainR) (hobs : Claim153ObsR)
    (hn : Claim153NormalR) (h1411 : Item1411_1R) (h155 : Item155R)
    (hWloc : Claim1411NonsolvWR) (hXloc : Claim1411NonsolvXR) (h1444 : Item1444S14)
    (h146 : Item146S14) (hbot : Item145BotS14) (h142 : Concl142S14) (hU35 : Step163U35)
    (hRead : Y4CoreReadR) (hMem : Y4CoreMemR) (h148 : Item148SmallS14) (hCore : Step148Core)
    (hPoint : Step148Point) (hKT : Step148KType) (h135 : Item135) (hOne : Step162UJOddOne)
    (hFree : Step162A7OtherFreeMeet) : Item162R :=
  item162R_of_res6_core h1514 h1523 h153 hobs hn h1411 h155 hWloc h1444 h146 hbot h142 hU35
    hRead hMem h148 hCore hPoint hKT h135
    (step162UJOddProper_of_one h1514 h1523 h153 hobs h1411
      (step163MeetsPoint_of_steps148 hCore hPoint hKT) hXloc hOne)
    ks162J2TwoInner ks162J2NormSolv hFree

end CFSG.RankThree.PartTwo.Sec16
