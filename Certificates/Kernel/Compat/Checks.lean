module

public import Certificates.Data.Kernel.Compat
public import Certificates.Kernel.LocalQT.Syl.C4137
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.PairData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.PairB0

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.Compat

open CFSG.KC.Ord CFSG.KC.Compat CFSG.KD.LQT.C4137 CFSG.QuasithinUnique.Setup.X1
  CFSG.EvenSporadicStandard.M24Std

theorem ch24853 : compatK GC m24RGens m24E1Bw m24B0Bw pairYW = true := by quickRfl

end CFSG.KD.Compat

end
