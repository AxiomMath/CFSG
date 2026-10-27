module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Split
public import CFSG.LocalAnalysis.StandardType.FS81.N5N0
public import CFSG.LocalAnalysis.StandardType.FS81.N7N0

public section

namespace CFSG.StandardType.FrameRoute.FS81

theorem t5N0_holds : T5N0 := fun _ _ _ _ _ _ _ B hB _ hfus hodd hN0 =>
  false_of_evenN0_five (B.evenN0MatHyp_xg hB.2.1 hN0 (hB.1.symm ▸ hodd) hfus)

end CFSG.StandardType.FrameRoute.FS81

end
