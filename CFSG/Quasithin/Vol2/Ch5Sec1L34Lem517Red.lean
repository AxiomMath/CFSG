module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem517
public import CFSG.Quasithin.Vol2.Ch5Sec1L34OddTIMp
public import CFSG.Quasithin.Vol2.Ch5Sec1L34OddNoBlock
public import CFSG.Quasithin.Vol2.Ch5Sec1L34OddAmal
public import CFSG.Quasithin.Vol2.KGFactL34Aut

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

theorem stmt5_1_17_of_reduced
    (hI : L2OddInnerFact) (hL : L34SylowNormFact) (hF : L2TorusFact)
    (h515 : Stmt5_1_15) (h516 : Stmt5_1_16) (hIrr : IrrPlusBaseNonempty) (h323 : Stmt3_2_3)
    (h325 : Stmt3_2_5) (h3228 : Stmt3_2_2_eight) (h513 : Stmt5_1_3) (h5114 : Stmt5_1_14_first)
    (h510 : Stmt5_1_10) (hBor : L34BorelFact) (h517one : A5.Stmt5_1_7_one)
    (h126 : A126TwoFact) (hmNine : Stmt5_1_17_mNine) : Stmt5_1_17 :=
  stmt5_1_17_of_inputs hI hL hF h515 h516 hIrr h323 h325 h3228 h513 h5114 h510 hBor
    (stmt5_1_17_TI_of hI hF h5114 h517one) (stmt5_1_17_abelian_proved hI hF h5114 h126)
    (stmt5_1_17_amalgam_of hI hmNine l34AutTwoRankFact_holds)

end CFSG.Quasithin.H13
