module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res2Proof
public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofA6
public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofA7M22
public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofIn
public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofL2
public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofL3
public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofLieP
public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofAlt
public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofSpor
public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofChevTwo
public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofSmallTwo
public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofCharThree
public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofCenters
public import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofA8
public import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofA9
public import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofL3
public import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofLieP
public import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofU54
public import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofL52
public import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofSp62
public import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofJ3
public import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofU54Datum
public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofON
public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofG2
public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofInU43
public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofOut
public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofCharThree
public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofChevTwo
public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofCover
public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofU43
public import Certificates.Certificate8007
public import Certificates.Certificate8008
public import Certificates.Kernel.J4Count.Cent11Base
public import Certificates.Kernel.J4Count.Fix11

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo Res417Three Res417Four
open Res417Five

theorem item417InU43McLRest_of_mcl
    (hMcL : K417E81McL) : Item417InU43McLRest :=
  item417InU43McLRest_of (k417CoverE35_of hMcL k417E81U43_holds)

theorem item417OutMcL_of_mcl
    (hMcL : K417E81McL) : Item417OutMcL :=
  item417OutMcL_of hMcL

theorem item4_17_of_res5
    (h45 : Item4_5) (h47 : Item4_7) (h43 : Item4_3) (h46 : Item4_6)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hJ3 : Item417InJ3Rest) (hG2c : K417G2CoverCent) (hL3 : K417NoActLThreeThree)
    (hSpOdd : K417NoDatumSp4Odd) (hSpEven : K417DatumSp4Even) (hUEven : K417DatumU4Even)
    (hUOdd : K417DatumU4Odd) (hGOdd : K417NoDatumG2D4Odd) (hGEven : K417DatumG2D4Even)
    (hF4 : K417NoDatumF4) (hMcL : K417E81McL) (hG23 : K417E81G23) : Item4_17 :=
  item4_17_of_res2 h45 h47 h43 h46 hGA item417InA6_holds item417InA7M22_holds
      (item417InG2_of hGA (item417InG2Rest_of hG2c))
      (item417InU43McL_of hGA (item417InU43McLRest_of_mcl hMcL)) (item417InJ3_of hJ3)
      (item417InON_of item417InONRank_holds) item417OutL2_holds
      (item417OutL3Eps_of k417RankOneL3_holds k417RankOneU3_holds)
      (item417OutLieP_of k417RankTwoLieP_holds (k417CenterLieP_of_griess hGA))
      (item417OutAlt_of k417OutA8_holds k417OutA9_holds)
      (item417OutSpor_of k417OutJ3_holds (item417OutMcL_of_mcl hMcL))
      (item417OutChevTwo_of k417RankOneU3_holds (k417CenterChevTwo_of_griess hGA)
          (k417DatumChevTwo_of hSpOdd hSpEven hUEven hUOdd hGOdd hGEven hF4))
      (item417OutSmallTwo_of (k417CenterSmallTwo_of_griess hGA k417CenterU54_holds)
          (k417DatumSmallTwo_of k417DatumU54_holds k417DatumSp62_holds))
      (item417OutCharThree_of (item417OutCharThreeRest_of hGA hL3 hG23 k417E81U43_holds))

end CFSG.RankThree.PartTwo.Sec4
