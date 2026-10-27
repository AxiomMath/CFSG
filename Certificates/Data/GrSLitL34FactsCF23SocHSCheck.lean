module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutOuterCheckInputs
public import CFSG.Sporadic.SmallOddCore.HSAut

public section

namespace CFSG.ComponentClassification.GSThmB.Soc

open CFSG.PSL3Four.Native CFSG.QuasithinUnique.Id2519.HSAut

@[expose] def hsW1 : Tab := comp 3850 e1Tab e2Tab

@[expose] def hsW2 : Tab := comp 3850 hsW1 hsW1

@[expose] def hsW3 : Tab := comp 3850 hsW2 hsW1

@[expose] def hsW6 : Tab := comp 3850 hsW3 hsW3

@[expose] def hsOrderSixOK : Bool :=
  hsW6 == idTab 3850 && !(hsW2 == idTab 3850) && !(hsW3 == idTab 3850)

end CFSG.ComponentClassification.GSThmB.Soc
