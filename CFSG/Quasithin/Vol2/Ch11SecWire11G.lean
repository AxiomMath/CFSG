module

public import CFSG.Quasithin.Vol2.Ch11G2Q8N13
public import CFSG.Quasithin.Vol2.KGNatSp4Levi
public import CFSG.Quasithin.Vol2.KGNatSp4N13
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.Vol2.Ch11.Wire11

theorem natFacts : SecA.NatFacts :=
  ⟨KGNat.factFlagSL3_holds, KGNat.factFlagSp4_holds, G2Q8.factFlagG2_holds, KGNat.factLeviSL3_holds,
    KGNat.factLeviSp4_holds, G2Q8.factLeviG2_holds, KGNat.factN13Sp4_holds, G2Q8.factN13G2_holds⟩

end CFSG.Quasithin.Vol2.Ch11.Wire11
