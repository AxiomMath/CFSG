module

public import CFSG.RankThree.PartTwo.Sec17.RouteWire14
public import CFSG.RankThree.PartTwo.Sec17.RouteWire15
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsRoute
import CFSG.RankThree.PartTwo.KFacts.KS14OrdersSpor
public import CFSG.RankThree.PartTwo.Sec17.Item175Proof

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec15

theorem item1411_3R_of_hj_wired
    (h146 : Item146S14) (hbot : Item145BotS14) (h142 : Concl142S14) (hN : Item1411_3NHJR) :
    Item1411_3R :=
  fun G _ _ A c L hR => item1411_3_of_hj_wired hR (h146 G A c L hR.toSec14Std)
    (hbot G A c L hR.toSec14Std) (h142 G A c L hR.toSec14Std) (hN G A c L hR)

end CFSG.RankThree.PartTwo.Sec14

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec17

theorem claim153NormalR_of_wired (h152 : Item152R) (hno : Claim153NormalNoE9R) :
    Claim153NormalR :=
  fun G _ _ A c L hR => claim153Normal_of_wired hR.toSec14Std (h152 G A c L hR) (hno G A c L hR)

theorem claim153ObsR_of_wired (h149 : Sec16.Item149S14) (hn : Claim153NormalR) : Claim153ObsR :=
  fun G _ _ A c L hR => claim153Obs_of_normal hR.toSec14Std (h149 G A c L hR.toSec14Std)
    (hn G A c L hR)

theorem item1511S17_of_wired (h : Item1511R) : Item1511S17 :=
  fun G _ _ A c L _ hs => h G A c L hs.toSec15R

theorem item1513S17_of_wired (h : Item1513R) : Item1513S17 :=
  fun G _ _ A c L _ hs => h G A c L hs.toSec15R

theorem item1512R_of_wired (h131 : Item131)
    (hspor : SporadicModels131) (hSLC : SLTwoCenter) (hgen : KS15M22Gen) (h159 : Item159R)
    (h1411 : Item1411_1R) (h153 : Item153MainR) (hobs : Claim153ObsR) : Item1512R :=
  fun G _ _ A c L hR => rank3II_15_12_of_main h131 hspor hSLC
    (fun p e _ => KFacts.KS14.not_isoLThreePi_M22 p e)
    (fun p f _ => KFacts.KS14.not_isLThreeEpsAt_M22 p f)
    KFacts.KS14.isEmpty_mulEquiv_M22_alternating.2.1 KFacts.KS14.isEmpty_mulEquiv_M22_M12
    KFacts.KS14.isEmpty_mulEquiv_M22_J2 CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2 hgen hR
    (h159 G A c L hR) (h1411 G A c L hR) (h153 G A c L hR) (hobs G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
