module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PWire
public import CFSG.RankThree.PartTwo.Sec15.Gagen148FourKHolds
public import CFSG.RankThree.PartTwo.Sec15.LiebeckClosed
public import CFSG.RankThree.PartTwo.Sec15.Item15Res6ProofExcl
public import CFSG.RankThree.PartTwo.Sec15.F153MainObs8
import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofProd
import CFSG.RankThree.PartTwo.Sec15.Item154PiProof
import CFSG.RankThree.PartTwo.Sec13.Ronan137Holds

public section

namespace CFSG.RankThree.PartTwo.Sec15.Closed155W9

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14


theorem item155wR_of_open
    (h152 : Item152R) (h153 : Item153MainR) (h154 : Item154PiR)
    (h316 : Sec19.Item316) (htwo : Step155CasesTwoNHJWR)
    (hst : StellmacherKP) (hY4 : Y4CoreMemR)
    (hfr : Step155FrattiniNWPR) : Item155wR := by
  obtain ⟨-, h48, -, -, -, -, -, -, h134, -, -⟩ := Ronan148M.closedInputs
  exact item155wR_of_corr9Cert h152 h153 h154 item3_15_holds h316 Ronan149.item1444S14_holds
    Proof148FourK.item146S14_holds Ronan149.item145BotS14_holds Ronan149.item149S14_holds
    Ronan148M.concl142S14_holds Ronan148M.item148R_holds h134 h48
    LiebeckClosed.step155UpPiNHJR_holds Ronan155Y.step155GrowAltTwoFieldWR_holds
    Proof148FourK.step155YQ0HypWR_holds Proof148FourK.step155PJQ0HypWR_holds htwo hst
    Ronan148M.concl143S14_holds hY4 hfr

theorem item156R_of_open (h152 : Item152R) (h316 : Sec19.Item316)
    (h1411 : Item1411_1R) (h154 : Item154PiR) (hpush : Step153CharPush)
    (hrest : Step156CQA5DFaithR) (htwo : Step155CasesTwoNHJWR)
    (hst : StellmacherKP) (hY4 : Y4CoreMemR)
    (hfr : Step155FrattiniNWPR) : Item156R := by
  obtain ⟨-, h48, -, -, -, -, -, -, h134, -, h142⟩ := Ronan148M.closedInputs
  exact item156R_of_steps155w9Cert Ronan148M.item148R_holds h152 Ronan149.item149S14_holds
    item3_15_holds h316 h1411 h134 h48 h142 h154 Ronan149.item1444S14_holds
    Proof148FourK.item146S14_holds Ronan149.item145BotS14_holds hpush hrest
    Ronan148M.concl142S14_holds LiebeckClosed.step155UpPiNHJR_holds
    Ronan155Y.step155GrowAltTwoFieldWR_holds Proof148FourK.step155YQ0HypWR_holds
    Proof148FourK.step155PJQ0HypWR_holds htwo hst Ronan148M.concl143S14_holds hY4 hfr

theorem item155R_of_open (h152 : Item152R) (h316 : Sec19.Item316)
    (h1411 : Item1411_1R) (h154 : Item154PiR) (hpush : Step153CharPush)
    (hrest : Step156CQA5DFaithR) (htwo : Step155CasesTwoNHJWR)
    (hst : StellmacherKP) (hY4 : Y4CoreMemR)
    (hfr : Step155FrattiniNWPR) : Item155R := by
  obtain ⟨-, h48, -, -, -, -, -, -, h134, -, h142⟩ := Ronan148M.closedInputs
  exact item155R_of_steps155w9Cert Ronan148M.item148R_holds h152 Ronan149.item149S14_holds
    item3_15_holds h316 h1411 h134 h48 h142 h154 Ronan149.item1444S14_holds
    Proof148FourK.item146S14_holds Ronan149.item145BotS14_holds hpush hrest
    Ronan148M.concl142S14_holds LiebeckClosed.step155UpPiNHJR_holds
    Ronan155Y.step155GrowAltTwoFieldWR_holds Proof148FourK.step155YQ0HypWR_holds
    Proof148FourK.step155PJQ0HypWR_holds htwo hst Ronan148M.concl143S14_holds hY4 hfr

section Frontier


theorem item155wR_of_frontier
    (hSL25 : Y4CoreExclSL25HJR) (h135 : Item135)
    (h316 : Sec19.Item316) (h154 : Item154R) (htwo : Step155CasesTwoNHJWR)
    (hst : StellmacherKP) (hfr : Step155FrattiniNWPR) :
    Item155wR := by
  obtain ⟨-, h48, -, -, -, h415, -, -, h134, -, h142⟩ := Ronan148M.closedInputs
  have h148 : Item148R := Ronan148M.item148R_holds
  have h149 : Sec16.Item149S14 := Ronan149.item149S14_holds
  have h152 : Item152R := item152R_of_compJ_excl h149 h148 h134 h48 h415 KFacts.kpSz
    (step152CompJNTR_of_item148R h148) hSL25
  have hchar : Claim153CharR := F153.claim153CharR_of_frontier_obs8 h316 h149 h148 h152 h134
    h135 Ronan137H.item137_holds h142 h48 h415 Ronan148M.concl142S14_holds
    Ronan148M.concl143S14_holds Proof148FourK.item146S14_holds Ronan149.item1444S14_holds
    Ronan149.item145BotS14_holds (item148HJS14_of_wired Ronan148M.item148S14_holds)
  exact item155wR_of_open h152
    (item153MainR_of_twin h149 (claim153TwinR_of_items h148 h149 h152) hchar)
    (item154PiR_of_steps h148 Ronan149.item145BotS14_holds h134 h48 Ronan148C.step148Core_holds
      Ronan148M.step148Point_holds Ronan148M.step148KType_holds Ronan148M.step148Lift_holds
      Ronan148M.step148D4_holds step148KTypeSigma_holds h154)
    h316 htwo hst
    (y4CoreMemR_of_excl h149 LiebeckClosed.y4CoreMemSolvR_holds h134 h48 h148 hSL25) hfr

theorem item156R_of_frontier (hSL25 : Y4CoreExclSL25HJR)
    (h135 : Item135) (h316 : Sec19.Item316) (h154 : Item154R) (h1411 : Item1411_1R)
    (hrest : Step156CQA5DFaithR) (htwo : Step155CasesTwoNHJWR)
    (hst : StellmacherKP) (hfr : Step155FrattiniNWPR) :
    Item156R := by
  obtain ⟨-, h48, -, -, -, h415, -, -, h134, -, h142⟩ := Ronan148M.closedInputs
  have h148 : Item148R := Ronan148M.item148R_holds
  have h149 : Sec16.Item149S14 := Ronan149.item149S14_holds
  have h152 : Item152R := item152R_of_compJ_excl h149 h148 h134 h48 h415 KFacts.kpSz
    (step152CompJNTR_of_item148R h148) hSL25
  have hchar : Claim153CharR := F153.claim153CharR_of_frontier_obs8 h316 h149 h148 h152 h134
    h135 Ronan137H.item137_holds h142 h48 h415 Ronan148M.concl142S14_holds
    Ronan148M.concl143S14_holds Proof148FourK.item146S14_holds Ronan149.item1444S14_holds
    Ronan149.item145BotS14_holds (item148HJS14_of_wired Ronan148M.item148S14_holds)
  exact item156R_of_open h152 h316 h1411
    (item154PiR_of_steps h148 Ronan149.item145BotS14_holds h134 h48 Ronan148C.step148Core_holds
      Ronan148M.step148Point_holds Ronan148M.step148KType_holds Ronan148M.step148Lift_holds
      Ronan148M.step148D4_holds step148KTypeSigma_holds h154)
    (step153CharPush_of_charR hchar) hrest htwo hst
    (y4CoreMemR_of_excl h149 LiebeckClosed.y4CoreMemSolvR_holds h134 h48 h148 hSL25) hfr

theorem item155R_of_frontier (hSL25 : Y4CoreExclSL25HJR)
    (h135 : Item135) (h316 : Sec19.Item316) (h154 : Item154R) (h1411 : Item1411_1R)
    (hrest : Step156CQA5DFaithR) (htwo : Step155CasesTwoNHJWR)
    (hst : StellmacherKP) (hfr : Step155FrattiniNWPR) :
    Item155R := by
  obtain ⟨-, h48, -, -, -, h415, -, -, h134, -, h142⟩ := Ronan148M.closedInputs
  have h148 : Item148R := Ronan148M.item148R_holds
  have h149 : Sec16.Item149S14 := Ronan149.item149S14_holds
  have h152 : Item152R := item152R_of_compJ_excl h149 h148 h134 h48 h415 KFacts.kpSz
    (step152CompJNTR_of_item148R h148) hSL25
  have hchar : Claim153CharR := F153.claim153CharR_of_frontier_obs8 h316 h149 h148 h152 h134
    h135 Ronan137H.item137_holds h142 h48 h415 Ronan148M.concl142S14_holds
    Ronan148M.concl143S14_holds Proof148FourK.item146S14_holds Ronan149.item1444S14_holds
    Ronan149.item145BotS14_holds (item148HJS14_of_wired Ronan148M.item148S14_holds)
  exact item155R_of_open h152 h316 h1411
    (item154PiR_of_steps h148 Ronan149.item145BotS14_holds h134 h48 Ronan148C.step148Core_holds
      Ronan148M.step148Point_holds Ronan148M.step148KType_holds Ronan148M.step148Lift_holds
      Ronan148M.step148D4_holds step148KTypeSigma_holds h154)
    (step153CharPush_of_charR hchar) hrest htwo hst
    (y4CoreMemR_of_excl h149 LiebeckClosed.y4CoreMemSolvR_holds h134 h48 h148 hSL25) hfr

end Frontier

end CFSG.RankThree.PartTwo.Sec15.Closed155W9
