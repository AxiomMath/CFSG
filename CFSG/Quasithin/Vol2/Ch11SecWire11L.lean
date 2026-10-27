module

public import CFSG.Quasithin.Vol2.Ch11SecU1EpsOut
public import CFSG.Quasithin.Vol2.Ch11SecBHBMainC
public import CFSG.Quasithin.Vol2.Ch11SecBK1A
public import CFSG.Quasithin.Vol2.Ch11SecBK1B
public import CFSG.Quasithin.Vol2.KGNatSL3PointB
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch11G2Q8ParG2
public import CFSG.Quasithin.Vol2.Ch11SecKGBorelComm
public import CFSG.Quasithin.Vol2.Ch11SecU1Wire
public import CFSG.Quasithin.Vol2.KGNatSL3PointT

public section

namespace CFSG.Quasithin.Vol2.Ch11.Wire11

theorem pointFacts : SecB.PointFacts :=
  ⟨KGNat.factPointSL3B_holds, SecB.factPointSp4_holds, G2Q8.factPointG2B_holds,
    KGNat.factPointTSL3_holds, SecB.factPointTSp4_holds, G2Q8.factPointTG2_holds,
    KGNat.factParSL3_holds, SecB.factParSp4_holds, G2Q8.factParG2_holds⟩

theorem e114OneResRest : E2.E22N.E114OneResRest :=
  E2.E22N.e114OneResRest_holds

theorem e114OneRes (hE114OneResRest : E2.E22N.E114OneResRest) : E2.E22N.E114OneRes :=
  SecB.e114OneRes_of_rest hE114OneResRest

theorem derivedHallBorel (hE22StatementC : E2.E22StatementC) : SecB.DerivedHallBorel :=
  SecB.derivedHallBorel_ofC hE22StatementC SecB.factBorelComm_holds

end CFSG.Quasithin.Vol2.Ch11.Wire11
