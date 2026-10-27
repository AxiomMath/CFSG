module

public import CFSG.RankThree.PartTwo.Sec16.Item166StepsProof
public import CFSG.RankThree.PartTwo.Sec16.Item166ResProofTwoPow

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17

theorem item166S17_of_steps_not2n
    (h2 : Step166ThetaTwo) (h146 : Item146S14) (hΔ : Step166DeltaSz)
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) (hL3 : KSL3PiNoSz) (h165 : Item165S17)
    (hΩ : Step166OmegaNot2n) (hctr : Step166CtrNot2n) : Item166S17 :=
  item166S17_of_steps h2 h146 hΔ h1514 hMeets hL3 (step166Omega_of_not2n h165 hΩ)
    (step166Ctr_of_not2n h165 hctr)

end CFSG.RankThree.PartTwo.Sec16

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec16

theorem step168Two_of_not2n (hst : StellmacherKP)
    (h146 : Item146S14) (h166 : Item166S17) (hbot : Item145BotS17) (h167 : Item167R)
    (h165 : Item165S17) (hOut : Step168TwoOutNot2n) : Step168Two :=
  step168Two_of hst h146 h166 hbot h167 (step168TwoOut_of_not2n h165 hOut)

end CFSG.RankThree.PartTwo.Sec17
