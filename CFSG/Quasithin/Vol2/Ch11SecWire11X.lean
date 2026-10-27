module

public import CFSG.Quasithin.Vol2.Ch11SecD554
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch11SecD555
public import CFSG.Quasithin.Vol2.Ch11SecD557Cases
public import CFSG.Quasithin.Vol2.Ch11SecO1J

public section

namespace CFSG.Quasithin.Vol2.Ch11.Wire11

theorem stmt11_5_4 (h11_0_2 : Stmt11_0_2) (h11_0_3 : Stmt11_0_3) (h11_1_0 : Stmt11_1_0)
    (h11_1_2 : Stmt11_1_2) (h11_2_3 : Stmt11_2_3) (h11_4_1 : Stmt11_4_1) (h11_4_3 : Stmt11_4_3)
    (h11_5_3 : Stmt11_5_3) : Stmt11_5_4 :=
  SecD.stmt11_5_4_of KGNat.pointsTIFact_holds h11_0_3 h11_0_2 h11_1_0 h11_1_2 h11_2_3 h11_4_1
    h11_4_3 h11_5_3

theorem stmt11_5_5 (h11_0_2 : Stmt11_0_2) (h11_4_1 : Stmt11_4_1) (h11_5_1 : Stmt11_5_1) :
    Stmt11_5_5 :=
  SecD.stmt11_5_5_of SecD.natV3Fact_holds h11_0_2 h11_4_1 h11_5_1

theorem stmt11_5_7 (h11_5_1 : Stmt11_5_1) (h11_5_7SL3 : SecD.Stmt11_5_7SL3)
    (h11_5_7Sp4 : SecD.Stmt11_5_7Sp4) : Stmt11_5_7 :=
  SecD.stmt11_5_7_of_cases h11_5_1 h11_5_7SL3 h11_5_7Sp4

end CFSG.Quasithin.Vol2.Ch11.Wire11
