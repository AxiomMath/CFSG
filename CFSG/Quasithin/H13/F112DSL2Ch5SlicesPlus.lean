module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem518D5Plus
public import CFSG.Quasithin.H13.F112DSL2Ch5Slices
public import CFSG.Quasithin.Vol2.Ch5Sec1L34ParFact2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

theorem stmt5_1_18_D5_of_corrected_slicesPlus
    (hDSC : DSCStatementPlus)
    (h311 : Theorem311Stmt) (h5114 : Stmt5_1_14_first) (h510 : Stmt5_1_10) (h516 : Stmt5_1_16)
    (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK) (h314 : A314Facts)
    (hFive : A314FiveNormFact) : Stmt5_1_18_D5 :=
  stmt5_1_18_D5_of_inputs_plus l34TwoParabolicFact l34TwoAutFact l2TorusFact h311 h5114 h510 h516
    h331 hR hDSC h36 h37 h38 h39 h312 h314 hFive

theorem stmt5_1_18_of_f112_corrected_slicesPlus
    (hDSAL2 : DSAL2Statement) (hDSC : DSCStatementPlus)
    (h311 : Theorem311Stmt) (h5114 : Stmt5_1_14_first) (h432 : Stmt4_3_2) (h510 : Stmt5_1_10)
    (h515 : Stmt5_1_15) (h516 : Stmt5_1_16) (h517 : Stmt5_1_17) (h331 : Stmt3_3_1)
    (hR : L2RankOneSylowFact) (hF : F112L2FourChiefFactC) (hPC : L34ParabolicChiefFact)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h312 : A312ForSQTK) (h314 : A314Facts) (hFive : A314FiveNormFact) : Stmt5_1_18 :=
  stmt5_1_18_of_reduced_outer_corrected_slices l2TorusFact h510 h515 h516 h5114 h517 h432 h331 hR
    hDSAL2 hF hPC
    (stmt5_1_18_D5_of_corrected_slicesPlus hDSC h311 h5114 h510 h516 h331 hR h36 h37 h38 h39 h312
      h314 hFive)

end CFSG.Quasithin.H13
