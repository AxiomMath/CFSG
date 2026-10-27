module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.PairData
import CFSG.Certificates.Kernel.CompatSound
import Certificates.Kernel.Compat.Checks

public section

namespace Certificates

theorem certificate24853 : CFSG.EvenSporadicStandard.M24Std.CompatPairData ∧
    CFSG.EvenSporadicStandard.M24Std.CompatZData ∧
    CFSG.EvenSporadicStandard.M24Std.CompatYData :=
  CFSG.KC.Compat.compat_of CFSG.KD.LQT.C4137.hG CFSG.KD.Compat.ch24853

end Certificates
