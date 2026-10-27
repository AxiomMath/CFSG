module

public import CFSG.Quasithin.H13.NQCatL2LieParabolic
public import CFSG.Quasithin.H13.NQCatCartanGraph
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5111K1
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522Inputs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem stmt5_2_L2Lie_of_cat (hU3 : FactU3Cover) (hTwo : Stmt5_2_L2Two) (h510 : Stmt5_1_10) :
    Stmt5_2_L2Lie :=
  stmt5_2_L2Lie_of hU3 NQCat.factL2LieParabolic_holds hTwo h510

theorem stmt5_2_L2Gen_of_cat (h510 : Stmt5_1_10) : Stmt5_2_L2Gen :=
  stmt5_2_L2Gen_of NQCat.factL2LieParabolic_holds h510

theorem stmt5_2_1_par_of_cat (hTwo : Stmt5_2_L2Two) (h510 : Stmt5_1_10) : Stmt5_2_1_par :=
  stmt5_2_1_par_of NQCat.factL2LieParabolic_holds hTwo h510

theorem stmt5_2_6_borel_of_cat (hLie : Stmt5_2_L2Lie) (h510 : Stmt5_1_10) : Stmt5_2_6_borel :=
  stmt5_2_6_borel_of NQCat.factL2LieParabolic_holds hLie h510

theorem stmt5_2_L2Lie_of_inputs_cat
    (hU3 : FactU3Cover) (hRL : RankOneListedFacts.{0}) (h515 : Stmt5_1_5) (h510 : Stmt5_1_10) :
    Stmt5_2_L2Lie :=
  stmt5_2_L2Lie_of_inputs hU3 NQCat.factL2LieParabolic_holds hRL h515 h510

theorem rankTwoParabolicFact_holds : RankTwoParabolicFact :=
  rankTwoParabolicFact_of NQCat.factL2LieParabolic_holds

theorem stmt5_1_11_three_of_cat (h38 : Vol2Native.A38ForSQTKCat)
    (hRL : RankOneListedFacts.{0}) (hU3 : FactU3Cover) (h510 : Stmt5_1_10) : Stmt5_1_11_three :=
  stmt5_1_11_three_of NQCat.factL2LieParabolic_holds NQCat.factRank2CartanGraph_holds h38 hRL
    hU3 h510

theorem stmt5_2_2_of_cat
    (h515 : Stmt5_1_5) (h516 : Stmt5_1_6) (h510 : Stmt5_1_10) (h5111 : Stmt5_1_11)
    (h5113 : Stmt5_1_13C) (h5114 : Stmt5_1_14) (hU3 : FactU3Cover) (hRL : RankOneListedFacts.{0})
    (hbot : Stmt5_2_2_bot) (hne : Stmt5_2_2_ne) : Stmt5_2_2C :=
  stmt5_2_2_of_inputs h515 h516 h510 h5111 h5113 h5114 hU3 NQCat.factL2LieParabolic_holds hRL
    hbot hne

end CFSG.Quasithin.H13
