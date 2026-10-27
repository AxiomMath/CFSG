module

public import CFSG.RankThree.PartTwo.Sec13.K135TwoSix
public import CFSG.RankThree.PartTwo.Sec13.K135FourCube
public import CFSG.RankThree.PartTwo.Sec13.K135Multiplier
public import CFSG.RankThree.PartTwo.Sec13.K135K3
public import CFSG.RankThree.PartTwo.Sec13.K135MultPrimeFinal
public import CFSG.RankThree.PartTwo.Sec13.F135LastGlue
public import CFSG.RankThree.PartTwo.Sec13.F135LastR0
public import CFSG.RankThree.PartTwo.Sec13.F135LastR1
public import CFSG.RankThree.PartTwo.Sec13.K135OutTwoFinal
public import CFSG.RankThree.PartTwo.Sec13.K135SFGL12R3
public import CFSG.RankThree.PartTwo.Sec13.K135SFGL12R4
public import CFSG.RankThree.PartTwo.Sec13.K135SFGL12R5
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowLargePrime
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowMcLON

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

section

theorem item135A7OneTwoCrit2_of_kf135_gl12 (hLP : Sec4.Item4_1LargePrime)
    (hTC : Sec4.Item4_1ThreeCover) (hKF : KF135) (hMPG : K135SF.KFactMultPrimeGL12)
    (hOG : K135SF.KFactOutGL12) (hKFG : K135SF.KF135GL12) : Item135A7OneTwoCrit2 :=
  item135A7OneTwoCrit2_of_parts r0_holds r1_holds r2_holds
    (r3_holds_gl12 hLP hTC Sec4.Census.rank3II_4_2 kFactMultPrime_holds hMPG)
    (r4_holds_gl12 hLP hTC Sec4.Census.rank3II_4_2 (kFactG1_of_outTwo kFactOutTwo_holds)
      (K135SF.kFactG1GL12_of_outGL12 hOG))
    (r5_holds_gl12 hLP hTC Sec4.Census.rank3II_4_2 kFactMultPrime_holds hKF hMPG hKFG)
    kFactTwoSix_holds kFactFourCubeSeven_holds kFactMultiplier_holds kFactK3_holds

end

section

theorem item135A7OneTwoCrit2_of_kf135_gl12_closed (hKF : KF135) (hMPG : K135SF.KFactMultPrimeGL12)
    (hOG : K135SF.KFactOutGL12) (hKFG : K135SF.KF135GL12) : Item135A7OneTwoCrit2 :=
  let hGA := CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  item135A7OneTwoCrit2_of_kf135_gl12 (Sec4.Item41Narrow.item4_1LargePrime_of_griess hGA)
    (Sec4.Item41Narrow.item4_1ThreeCover_of_griess hGA) hKF hMPG hOG hKFG

end

end CFSG.RankThree.PartTwo.Sec13.F135Last
