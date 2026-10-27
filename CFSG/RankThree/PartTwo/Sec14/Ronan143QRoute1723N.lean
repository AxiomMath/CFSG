module

public import CFSG.RankThree.PartTwo.Sec17.RouteTopNarrow
public import CFSG.RankThree.PartTwo.Sec14.Ronan143Q163
public import CFSG.RankThree.PartTwo.Sec17.Item1723NRouteProofAssembly
import CFSG.RankThree.PartTwo.KFacts.KS44Sz
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec15.Read148PerfProof
import CFSG.RankThree.PartTwo.Sec16.Item162Res4ProofL
import CFSG.RankThree.PartTwo.Sec16.Item163ResProofMeets
import CFSG.RankThree.PartTwo.Sec16.Item165StepsProofClaim164
public import CFSG.RankThree.PartTwo.Sec15.Item152Narrow41
public import CFSG.RankThree.PartTwo.Sec17.Item1730Glue
public import CFSG.RankThree.PartTwo.Sec17.RouteJ2
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan143Q

section

open CFSG.RankThree.PartTwo.Sec17
open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late

theorem item1730_of_routeS16_narrowQ_1723N
    (h142N : Concl142NHJS14) (h143c : Concl143S14) (h143 : Ronan148Q.Item143NNHJ)
    (h1444 : Item1444S14) (h148 : Item148R)
    (hW1411 : Claim1411NonsolvWR) (hX1411 : Claim1411NonsolvXR)
    (hcomp : Step152CompR) (hexcl : Step152ExclR) (hconf : Step152ConfR) (hend : Step152EndR)
    (h1515 : Step1515S17) (h1519 : Step1519S17) (h1521 : Step1521S17) (h1522 : Step1522S17)
    (h1514 : Item1514R) (h1523 : Item1523R) (h153 : Item153MainR) (hobs : Claim153ObsR)
    (hn : Claim153NormalR) (h155 : Item155R) (h142All : Item142AllS14)
    (h148S : Item148SmallS14) (hCore : Step148Core) (hPoint : Step148Point)
    (hKT : Step148KType) (hMem : Y4CoreMemR) (h135 : Item135) (h1424 : Item14_24R)
    (h1510 : Item1510R) (h135S : Item135Simple) (h138 : Item138N)
    (h169 : Item169R) (h165 : Item165S17)
    (h166 : Item166S17) (h168 : Item168S17) (h172 : Item172S17) (h175 : Item175R)
    (h176 : Item176R) (h177 : Item177S17) (h1712 : Item1712S17) (hprod : ProdLBarS17)
    (hW1722 : Para1722) (hMeets : Claim1715Meets) (hAY : Claim1715A) (hW1719 : Claim1719W)
    (hC1718 : Claim1718) (h1721 : Item1721) (h1723 : Item1723N) (h1724 : Item1724N)
    (h134 : Item134) (hP : Sec4.Item4_1PRankLargePrime)
    (h48 : Sec4.Item4_8) (hst : CFSG.RankThree.PartTwo.StellmacherKP)
    (hgen : KS152HJGen) (h131 : Item131) :
    Item1730 := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have h142 : Concl142S14 := concl142S14_of_nhj h142N
  have h146 : Item146S14 := item146S14_of h142 h143c
  have hbot : Item145BotS14 := item145BotS14_of h134 h48 h415
  have hbot17 : Item145BotS17 := item145BotS17_of hbot
  have h1411 : Item1411_1R := item1411_1R_of (claim1411LocalR_of h146 hbot hW1411 hX1411)
  have h163 : Item163R := Ronan143Q.item163R_of_routes_coreQ h1514 h1523 h153 hobs hn h155 hW1411
    hX1411
    h142 h142All h143c h143 h1444 h146 hbot h148 h148S hCore hPoint hKT
    (Read148Perf.y4CoreReadR_from_item148R KFacts.kpSz hbot h148) hMem h131 h135 h1424 h1510
    h135S h138
  have h164 : Item164R := item164R_of_route h415 h131 sporadicModels131 h138 h1514 h163
    (step163Meets_of_point h1514 h1523 h153 hobs h1411
      (step163MeetsPoint_of_steps148 hCore hPoint hKT))
  have h152 : Item152R :=
    Sec15.item152R_narrow h148 h1411 h134 h48 h415 hst hcomp hexcl hconf hgen hend
  have h1713 : Item1713S17 := item1713S17_of h1712 h172
  have h1710 : Item1710S17 :=
    item1710S17_of h166 hbot17 h168 (item179S17_of h166 hbot17 h168 h146 h177)
  have h1725 : Item1725 :=
    item1725_of_named_1723N h1710 h1712 h166 hbot h1723 (item1724Three_of_item1724N h1724)
  have h1728 : Item1728 := item1728_of_steps_named_1723N h169 h163 h164
    (claim17MR_of h163 h152) h175 h176
    (para1714_of_named h1713 h166 hbot17 h168 (item1411_1S17_of h1411)) hW1722
    (item1715_narrow_named (item1514S17_of h1515 h1519 h1521 h1522)
      (item1714S17_of h1713 h165) hP hMeets hAY)
    (item1719_of_named hW1719 (item1718_of hC1718) h1712 h1710 h166 hbot17
      (cardInfNineS17_of hprod))
    h1721 h1723 h1724 h1725
  exact rank3II_17_30_of h1728 (ks17HJConjugacy_of_items h131 h134 h48 h415)
    (step1730Chosen_of_j2 h131 sporadicModels131 slTwoCenter h134 h48 h415
      KFacts.KS14.ks17J2NotList)

end

end CFSG.RankThree.PartTwo.Sec14.Ronan143Q
