module

public import CFSG.RankThree.PartTwo.Sec14.Ronan143Q1411Steps
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res5ProofRoute
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res6ProofOne
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res6Proof1420
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res6ProofCent
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res7ProofRoute
public import CFSG.RankThree.PartTwo.Sec14.Item1418Res2Proof1422
public import CFSG.RankThree.PartTwo.Sec14.Item1418Res3ProofRoute
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3Proof1418
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofM22
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res4ProofL3
public import CFSG.RankThree.PartTwo.Sec14.Item1418Res3ProofWGamma

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan143Q

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem item1411_3NHJR_of_res6Q'
    (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) (h146 : Item146S14) (hbot : Item145BotS14)
    (hpt : Claim1411NonsolvXPointL3R) (h131 : Item131) (h133 : Item133) (h134 : Item134)
    (h135 : Item135) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (h142 : Concl142S14)
    (h142All : Item142AllS14) (h143 : Ronan148Q.Item143QS14) (h1413 : Item1413CR)
    (hUniq : Step1418UniqR) (hSR : Step1422SR) : Item1411_3NHJR := by
  have hPGL := item1412NotPGLR_of h131 h142All hbot
  have h1416 := item1416R_of h142 h146 hbot
  have h1417 := item1417_2R_ofQ h134 h48 h415 h143 h146 hbot h1416
  have h1418 := item1418R_of_uniq h1417 hUniq
  have h1419 := item1419R_of_c h1413 h135 h142 hbot h131 h133 h1416 hPGL h1418 h422 h45
    ks1419LThreePi
  have hSne := step1420A7SneR_of_cQ h1413 h142 hbot h131 h1419 h143
  have hA7 := step1420A7TwoR_of_c h1413 h142 hbot h131 h1418 h1419 hSne
  have hM12 := step1421M12R_of_c h131 h1413 h135 h142
  have h1420 := item1420R_of_1419Q h131 h133 h1416 hPGL h1419 hA7 hM12 h422 h45 h134 h48 h415
    h143 h146 hbot
  have hCe := step1422CentR_of_c h1413 h135 h142 hbot h131 ks1422M22Cent
  exact item1411_3NHJR_of_F h422 h45 h146 hbot
    (claim1411NonsolvXCentFR_of_pointQ h131 h142All h142 h143 h146 hbot h422 h45
      (claim1411NonsolvXPointFR_of_l3 h131 hpt))
    (step1421R_of_1418Q h131 h133 h1418 h1419 h1420 hM12 h422 h45 h134 h48 h415 h143 h146 hbot)
    (step1422R_of_1418Q h131 h133 h1418 h1419 h1420 hM12 h422 h45 h134 h48 h415 h143 h146 hbot
      hCe hSR)

theorem item1411_3NHJR_of_res6Q
    (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) (h146 : Item146S14) (hbot : Item145BotS14)
    (hpt : Claim1411NonsolvXPointL3R) (h131 : Item131) (h133 : Item133) (h134 : Item134)
    (h135 : Item135) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (h142 : Concl142S14)
    (h142All : Item142AllS14) (h143 : Ronan148Q.Item143QS14) (hCL3 : Item1413CL3R)
    (hUniq : Step1418UniqR) (hSR : Step1422SR) : Item1411_3NHJR :=
  item1411_3NHJR_of_res6Q' h422 h45 h146 hbot hpt h131 h133 h134 h135 h48 h415 h142 h142All h143
    (item1413CR_of h131 h142All h142 h146 hbot hCL3) hUniq hSR

theorem item1411_3NHJR_of_res7Q
    (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) (h146 : Item146S14) (hbot : Item145BotS14) (h131 : Item131)
    (h133 : Item133) (h134 : Item134) (h135 : Item135) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (h142 : Concl142S14) (h142All : Item142AllS14)
    (h143 : Ronan148Q.Item143QS14) (hUniq : Step1418UniqR) (hSR : Step1422SR) : Item1411_3NHJR :=
  item1411_3NHJR_of_res6Q h422 h45 h146 hbot (claim1411NonsolvXPointL3R_of_res7 h131 h142All hbot)
    h131 h133 h134 h135 h48 h415 h142 h142All h143 (item1413CL3R_of_res7 h131 h142All hbot)
    hUniq hSR

theorem item1411_3NHJR_of_res8Q
    (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) (h146 : Item146S14) (hbot : Item145BotS14) (h131 : Item131)
    (h133 : Item133) (h134 : Item134) (h135 : Item135) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (h142 : Concl142S14) (h142All : Item142AllS14)
    (h143 : Ronan148Q.Item143QS14) (h1411 : Item1411_1FR) (hOff : Step1418OffR)
    (hIQB : Step1422IQBR) (hSIQ : Step1422SIQR) : Item1411_3NHJR := by
  have h1413 := item1413CR_of_res7 h131 h142All h142 h146 hbot
  have hUniq := step1418UniqR_of_off h422 h45 h1411 h1413 h142 hbot hOff
  have hPGL := item1412NotPGLR_of h131 h142All hbot
  have h1416 := item1416R_of h142 h146 hbot
  have h1417 := item1417_2R_ofQ h134 h48 h415 h143 h146 hbot h1416
  have h1418 := item1418R_of_uniq h1417 hUniq
  have h1419 := item1419R_of_c h1413 h135 h142 hbot h131 h133 h1416 hPGL h1418 h422 h45
    ks1419LThreePi
  have hSne := step1420A7SneR_of_cQ h1413 h142 hbot h131 h1419 h143
  have hA7 := step1420A7TwoR_of_c h1413 h142 hbot h131 h1418 h1419 hSne
  have hM12 := step1421M12R_of_c h131 h1413 h135 h142
  have h1420 := item1420R_of_1419Q h131 h133 h1416 hPGL h1419 hA7 hM12 h422 h45 h134 h48 h415
    h143 h146 hbot
  have hNW := step1422NotWHR_ofQ h131 h133 h1418 h1419 h1420 hM12 h422 h45 h134 h48 h415 h143
    h146 hbot
  exact item1411_3NHJR_of_res7Q h422 h45 h146 hbot h131 h133 h134 h135 h48 h415 h142 h142All
    h143 hUniq (step1422SR_of_iq h131 h133 h142 hNW hIQB hSIQ)

theorem item1411_3NHJR_of_res8Q'
    (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) (h146 : Item146S14) (hbot : Item145BotS14) (h131 : Item131)
    (h133 : Item133) (h134 : Item134) (h135 : Item135) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (h142 : Concl142S14) (h142All : Item142AllS14)
    (h143 : Ronan148Q.Item143QS14) (hWΓ : Step1411WGammaR) (hOff : Step1418OffR)
    (hIQB : Step1422IQBR) (hSIQ : Step1422SIQR) : Item1411_3NHJR :=
  item1411_3NHJR_of_res8Q h422 h45 h146 hbot h131 h133 h134 h135 h48 h415 h142 h142All h143
    (item1411_1FR_of_gammaQ h134 h48 h415 h143 h146 hbot (item1416R_of h142 h146 hbot) hWΓ) hOff
    hIQB hSIQ

open Proof1418Res3 in
theorem item1411_3NHJR_of_res9Q
    (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) (h146 : Item146S14) (hbot : Item145BotS14) (h131 : Item131)
    (h133 : Item133) (h134 : Item134) (h135 : Item135) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (h142 : Concl142S14) (h142All : Item142AllS14)
    (h143 : Ronan148Q.Item143QS14) (hWΓ : Step1411WGammaR) (hOff : Step1418OffLayerR)
    (hIQB : Step1422IQBLayerR) (hSIQ : Step1422SIQR) : Item1411_3NHJR :=
  item1411_3NHJR_of_res8Q' h422 h45 h146 hbot h131 h133 h134 h135 h48 h415 h142 h142All h143
    hWΓ (step1418OffR_of_layer hOff) (step1422IQBR_of_layer h131 hIQB) hSIQ

open Proof1418Res3 in
theorem item1411_3NHJR_of_res10Q
    (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) (h146 : Item146S14) (hbot : Item145BotS14) (h131 : Item131)
    (h133 : Item133) (h134 : Item134) (h135 : Item135) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (h142 : Concl142S14) (h142All : Item142AllS14)
    (h143 : Ronan148Q.Item143QS14) (hWΓ : Step1411WGammaLaR) (hOff : Step1418OffLayerR)
    (hIQB : Step1422IQBLayerR) (hSIQ : Step1422SIQR) : Item1411_3NHJR :=
  item1411_3NHJR_of_res9Q h422 h45 h146 hbot h131 h133 h134 h135 h48 h415 h142 h142All h143
    (step1411WGammaR_of_la h422 h45 (item1413CR_of_res7 h131 h142All h142 h146 hbot) h142All
      hbot hWΓ) hOff hIQB hSIQ

end CFSG.RankThree.PartTwo.Sec14.Ronan143Q
