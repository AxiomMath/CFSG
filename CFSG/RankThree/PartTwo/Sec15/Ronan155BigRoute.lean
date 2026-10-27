module

public import CFSG.RankThree.PartTwo.Sec15.Ronan155BigDefs
public import CFSG.RankThree.PartTwo.Sec15.Ronan153BigDefs
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315xQ
public import CFSG.RankThree.PartTwo.Sec15.SimsBaumannMain
import CFSG.RankThree.PartTwo.Sec15.Sylow155KSL3
import CFSG.RankThree.PartTwo.Sec15.Gagen148FourKHolds
public import CFSG.RankThree.PartTwo.Sec15.LiebeckClosed
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KS155.J2E4
import CFSG.RankThree.PartTwo.Sec15.Ronan155BigCases
import CFSG.RankThree.PartTwo.Sec15.Ronan155BigMain
import CFSG.RankThree.PartTwo.Sec15.Ronan155BigRQ
import CFSG.RankThree.PartTwo.Sec15.Gagen155BXW
public import CFSG.RankThree.PartTwo.Sec15.Gagen155INorm
public import CFSG.RankThree.PartTwo.Sec15.Gagen155W315xDefs
public import CFSG.RankThree.PartTwo.Sec15.Item155w3ProofQ0
public import CFSG.RankThree.PartTwo.Sec15.Item155wProofCorr
public import CFSG.RankThree.PartTwo.Sec15.Item322ScopeProof
public import CFSG.RankThree.PartTwo.Sec15.Item322ScopeProofRoute
public import CFSG.RankThree.PartTwo.Sec15.Sylow155StepDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan155Big

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

theorem item155wBigR_of_corr8Cert
    (h152 : Item152BigR) (h153 : Ronan153Big.Item153BigR) (h154 : Item154PiR)
    (h315 : Item3_15) (h316 : Sec19.Item316) (h1444 : Item1444S14)
    (h146 : Item146S14) (hbot : Item145BotS14) (h149 : Sec16.Item149S14)
    (h142 : Concl142S14) (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hKS155 : KS155J2CentE4) (hKSL3 : KSL3NonPiAutThree)
    (hUp : Step155UpPiNHJR) (halt : Step155GrowAltTwoFieldWR) (hYQ : Step155YQ0HypWR)
    (hPJQ : Step155PJQ0HypWR) (hY4 : Y4LThreePiNHJR) (hW315 : Step155W315xR)
    (hfr : Step155FrattiniNWPR) : Item155wBigR := by
  have hgrow := step155GrowWR_of h1444 h146 hbot (item154R_of_item154PiR h154)
    (step155GrowAltWR_of_two (step155GrowAltTwoWR_of_field h148 hbot h134 h48 hKSL3 halt))
  have hUp' := step155UpR_of_piR (step155UpPiR_of_nhj h148 hbot hUp)
  have hYQ' := step155YQ0WR_of h142 hYQ
  have hPJQ' := step155PJQ0WR_of h142 hPJQ
  have htwo := step155CasesTwoNHJWBigR_of_route hY4 h152 h153 hgrow h146 h1444 hbot hYQ' hPJQ'
  have hsubn := step155BSubn2WR_of h149
    (step155INormX2WR_of_rk (step155INormX2RkWR_of h148 h149))
  have hBXW := step155BXWR_of h148 h149
  exact fun G _ _ A c L hR => rank3II_15_5wN_of3x_big hR.toSec14Std (h152 G A c L hR)
    (h153 G A c L hR) (fun c' L' hc' hL' => h154 G A c' L' (sec15R_of_basePoint hR hc' hL'))
    h315 h316
    (fun hyp hQR hR2 hR1 => exists_char_normal_of_hyp322TwoJ item3_22TwoJ_holds hyp hQR hR2 hR1)
    (hUp' G A c L hR) (hgrow G A c L hR)
    (step155CasesNWBig_of (h146 G A c L hR.toSec14Std) (hYQ' G A c L hR) (hPJQ' G A c L hR)
      (step155CasesTwoWBig_of_nhj (h148 G A c L hR) (hbot G A c L hR.toSec14Std)
        (htwo G A c L hR))
      (step155CasesBWR_of hKS155 G A c L hR))
    (step155RQNWBig_of (h1444 G A c L hR.toSec14Std) (h146 G A c L hR.toSec14Std)
      (hbot G A c L hR.toSec14Std) (step155RQKWBig_of (h152 G A c L hR) (h153 G A c L hR)))
    (hBXW G A c L hR) (hW315 G A c L hR) (hsubn G A c L hR) (hfr G A c L hR)

section Closed


theorem item155wJ2R_of_big
    (h152 : Item152BigR) (h153 : Ronan153Big.Item153BigR)
    (h154 : Item154PiR) (h316 : Sec19.Item316) (hst : StellmacherKP) (hP : Step155W315PR)
    (hfr : Step155FrattiniNWPR) : Item155wJ2R := by
  obtain ⟨-, h48, -, -, -, -, -, -, h134, -, -⟩ := Ronan148M.closedInputs
  have h146 : Item146S14 := Proof148FourK.item146S14_holds
  have h1444 : Item1444S14 := Ronan149.item1444S14_holds
  have h148 : Item148R := Ronan148M.item148R_holds
  have h149 : Sec16.Item149S14 := Ronan149.item149S14_holds
  exact item155wJ2R_of_item155wBigR (item155wBigR_of_corr8Cert h152 h153 h154 item3_15_holds
    h316 h1444 h146 Ronan149.item145BotS14_holds h149 Ronan148M.concl142S14_holds h148 h134 h48
    CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155.ks155J2CentE4 kSL3NonPiAutThree
    LiebeckClosed.step155UpPiNHJR_holds Ronan155Y.step155GrowAltTwoFieldWR_holds
    Proof148FourK.step155YQ0HypWR_holds Proof148FourK.step155PJQ0HypWR_holds
    Ronan155Y.y4LThreePiNHJR_holds (step155W315xR_of_P hst h146 h1444 h148 h149 hP) hfr)

end Closed

end CFSG.RankThree.PartTwo.Sec15.Ronan155Big
