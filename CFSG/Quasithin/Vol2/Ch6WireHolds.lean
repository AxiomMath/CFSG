module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem8
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem8ResLie
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.E3
  CFSG.Quasithin.ASInputs
open CFSG.LieType.BorelTits

theorem stmt6_2_8_of_holds (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h6110 : Stmt6_1_10) (hE612 : Ch6InE612)
    (h627 : Stmt6_2_7) (hF : F713Two) : Stmt6_2_8 :=
  stmt6_2_8_of h331 h432 h512 h614 h615 h6110 hE612 h627 hF res628Lie_holds

end CFSG.Quasithin.H13
