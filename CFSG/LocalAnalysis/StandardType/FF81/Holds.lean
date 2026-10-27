module

public import CFSG.LocalAnalysis.StandardType.FF81.CentAHolds
public import CFSG.LocalAnalysis.StandardType.FF81.ConstructYAssembly
public import CFSG.LocalAnalysis.StandardType.FF81.CurtisA2
public import CFSG.LocalAnalysis.StandardType.FF81.FrameStep
public import CFSG.LocalAnalysis.StandardType.FF81.HoltEnd
public import CFSG.LocalAnalysis.StandardType.FF81.LocalSetup
public import CFSG.LocalAnalysis.StandardType.FF81.PropTwo
public import CFSG.LocalAnalysis.StandardType.FF81.Reduction
public import CFSG.LocalAnalysis.StandardType.FF81.RootFusionE6

public section

namespace CFSG.StandardType.FF81

theorem ff81bThmAAtFiveSixLab_of_propOne_centralizerE6
    (h1 : PropOne) (hE : CentralizerE6) : FF81bThmAAtFiveSixLab :=
  ff81bThmAAtFiveSixLab_of_pieces curtisA2_holds localSetup_holds h1 propTwo_holds frameStep_holds
    constructY_holds CentA.centralizerA_holds hE rootFusionE6_holds holtEnd_holds

end CFSG.StandardType.FF81

end
