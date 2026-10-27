module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanADefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveQ2PrimeLDefs

public section

namespace CFSG.StandardType

@[expose] def GGSecFiveDataResPhanAQTwoBInput :
    Prop :=
  GGSecFiveQ2PrimeLInput → GGSecFiveDataResPhanAQTwoInput

end CFSG.StandardType

end
