module

public import CFSG.RankThree.PartTwo.Sec4.Item417ResProofTwoMain
public import CFSG.RankThree.PartTwo.Sec4.Item417ResProofInner
public import CFSG.RankThree.PartTwo.Sec4.Item417ResProofOut
import CFSG.RankThree.PartTwo.Sec4.Item417Res2ProofOdd
import CFSG.RankThree.PartTwo.Sec4.Item417Res2ProofEven

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Certs

theorem item4_17_of_res2 (h45 : Item4_5) (h47 : Item4_7) (h43 : Item4_3) (h46 : Item4_6)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hA6 : Item417InA6) (hA7 : Item417InA7M22) (hG2 : Item417InG2) (hU43 : Item417InU43McL)
    (hJ3 : Item417InJ3) (hON : Item417InON)
    (h1 : Item417OutL2) (h2 : Item417OutL3Eps) (h3 : Item417OutLieP) (h4 : Item417OutAlt)
    (h5 : Item417OutSpor) (h6 : Item417OutChevTwo) (h7 : Item417OutSmallTwo)
    (h8 : Item417OutCharThree) : Item4_17 :=
  item4_17_of h45 h47
      (item4_17SL3Pi_of_frames hGA item417SL3FrameOdd_holds item417SL3FrameEven_holds
          item417L3FrameOdd_holds item417L3FrameEven_holds)
      (item4_17InnerIn_of hGA h43 hA6 hA7 hG2 hU43 hJ3 hON)
      (item4_17InnerOut_of h46 h1 h2 h3 h4 h5 h6 h7 h8)

end Certs

end CFSG.RankThree.PartTwo.Sec4
