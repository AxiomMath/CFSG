module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derA1Field
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derA1Block
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derOrth
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derExc

public section

namespace CFSG.StandardType.S2MathAs4B2der1822


theorem ggB2derSympKnown_holds : GGB2derSympKnown :=
  ggB2derSympKnown_of_sources linearNoB2derInput_holds unitaryNoB2derInput_holds
    orthNoB2derInput_holds exceptionalNoB2derInput_holds smallDerivedNoB2derInput_holds
    simpleSympFieldInput_holds symplecticBlockPositionInput_holds

end CFSG.StandardType.S2MathAs4B2der1822

end
