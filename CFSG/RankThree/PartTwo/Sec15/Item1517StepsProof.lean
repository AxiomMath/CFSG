module

public import CFSG.RankThree.PartTwo.Sec15.Item1517StepsProofSimple
public import CFSG.RankThree.PartTwo.Sec15.Item1517StepsProofY0
public import CFSG.RankThree.PartTwo.Sec15.Item1517StepsProofCon
public import CFSG.RankThree.PartTwo.Sec15.Item1517StepsProofP
public import CFSG.RankThree.PartTwo.Sec15.Item1517StepsProofCent

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14

theorem step1517R_of_named
    (h135 : Item135Simple) (h142 : Concl142R) (h152 : Item152R)
    (h1510 : Item1510R) (hbr : Sec16.Step169TwoBridge) (h138 : Item138N) (hgen : KS1517Gen)
    (h153 : Item153MainR) (hobs : Claim153ObsR) (h1411 : Item1411_1R) (hq0 : Step1517Q0) :
    Step1517R :=
  step1517R_of (step1517Y0_of h135 h142 h152 h1510 hbr h138 hgen)
    (step1517Con_of h153 hobs h1411 hq0) (step1517Simple_of h135)

theorem step1519R_of_named
    (h1518 : Step1518R) (h1517 : Step1517R)
    (h135 : Item135Simple) (h142 : Concl142R) (h1510 : Item1510R)
    (hbr : Sec16.Step169TwoBridge) (h138 : Item138N) (hcent : Step1519CentAut) :
    Step1519R :=
  step1519R_of h1518 (step1519Small_of_item138N h1510 hbr h138) (step1519P_of h135 h142)
    (step1519Cent_of h1517 h138 hcent)

end CFSG.RankThree.PartTwo.Sec15
