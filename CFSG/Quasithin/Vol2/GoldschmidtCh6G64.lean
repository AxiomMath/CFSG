module

public import CFSG.Quasithin.H13.GoldschmidtM22G64B56
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch6Remark612
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11T
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem12
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem5H
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem6
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem8
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem8ResLie

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.Quasithin.ASInputs

theorem stmt6_2_13_of_asB56 (hKu : StmtKuM22) (h56 : AsB56) (h311 : Theorem311Stmt)
    (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2) (h513 : Stmt5_1_3)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (hE63 : Ch6InE63) (hE612 : Ch6InE612)
    (hRes : Res627FF) (hF : F713Two) (hL : Res628Lie) (hG31 : Ch6G31O2) : Stmt6_2_13 := by
  have h6110 := stmt6_1_10 h311 h432 hE63
  have h6210 := (stmt6_2_8_and_10_of_res h331 h432 h512 h614 h615 h6110 hE612 hRes hF hL).2
  have h6211 := stmt6_2_11_of h331 h432 h512 h614 h615 h6210 hG31
  exact GM22.stmt6_2_13_of_b56 hKu h56 (stmt6_1_2 h512 h513) (stmt6_1_6 h331 h432 h512 h614 h615)
    h6110 (stmt6_2_1 h432) (stmt6_2_2 h331 h432 h512 h614 h615)
    (stmt6_2_5_of h331 h432 h615 h6110 hE612) (stmt6_2_6_of h331 h432 h615 h6110 hE612)
    (stmt6_2_7_of_res h331 h432 h615 h6110 hE612 hRes) (stmt6_2_9 h331 h432 h512 h614 h615)
    h6210 h6211 (stmt6_2_12_of h331 h432 h512 h614 h615 h6211)

theorem stmt6_2_13_of_holds_asB56 (hKu : StmtKuM22) (h56 : AsB56) (h311 : Theorem311Stmt)
    (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2) (h513 : Stmt5_1_3)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (hE63 : Ch6InE63) (hE612 : Ch6InE612)
    (hRes : Res627FF) (hF : F713Two) (hG31 : Ch6G31O2) : Stmt6_2_13 :=
  stmt6_2_13_of_asB56 hKu h56 h311 h331 h432 h512 h513 h614 h615 hE63 hE612 hRes hF
    res628Lie_holds hG31

end CFSG.Quasithin.H13
