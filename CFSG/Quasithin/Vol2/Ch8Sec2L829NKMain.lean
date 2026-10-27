module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKNonsolv
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKEasy
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKU3Five
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKRank
public import CFSG.Quasithin.Vol2.Ch8Sec2L829P7
public import CFSG.Quasithin.Vol2.Ch8Sec2L829KerLU

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs
  CFSG.Quasithin.H13 CFSG.Quasithin.H13.L829N

theorem step829L3M22_noKantor_of_leaves (hmod : StmtFSUModule) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h3228 : Stmt3_2_2_eight) (h325 : Stmt3_2_5) (h331 : Stmt3_3_1)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h711n : Stmt7_1_1_normal) (h825 : Stmt8_2_5)
    (h828 : Stmt8_2_8) (hE22 : E2.E22StatementNoN) (hD3 : StmtD3L3M22)
    (hLU : HLU82) (hcard : CFSG.Quasithin.H.Mathieu.StmtH13Card)
    (hD4 : L829N.StmtD4L3M22) (hS3 : Step828Three)
    (hSz : NKLeafSz) (hSzDvd : NKLeafSzDvd) (hU3Even : NKLeafU3Even)
    (hL3TwoOdd : NKLeafL3TwoOdd) (hL2Odd : NKLeafL2Odd) (hL3Odd : NKLeafL3Odd)
    (hU3Odd : NKLeafU3Odd)
    (hL32 : NKLeafL32) (hSch : NKLeafSchurL32) (hSL3 : NKLeafSL3Rep) : Step829L3M22 :=
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let hF : StmtFelemL3M22 :=
    stmtFelemL3M22_holds hmod h711n h825 hLU hcard
      (stmtKerLUOdd_holds hmod h711n h825 hLU hcard h828)
  step829L3M22_of' hmod h37 h38 h39 h3228 h325 h331 hC58 h317 h711n
    (l3M22Nonsolv_noKantor
      ⟨hSz, hSzDvd, hU3Even, nk_leafU3Five, hL3TwoOdd, hL2Odd, nk_leafL2TwentyFive, hL3Odd, hU3Odd,
        nk_leafU3FiveP, nk_leafL2Dvd3, nk_liftCase1 (by norm_num), nk_liftCase2 (by norm_num), hL32, hSch, hSL3⟩
      hmod h37 h38 h39 h3228 h325 h331 hC58 h317 h711n h825 h828 hE22 hD3 hF hD4 hS3)
    (l3M22Solv_of hmod h711n h825 h828 hD3 hF)

end CFSG.Quasithin.H13.L829NK
