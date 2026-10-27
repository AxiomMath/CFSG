module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.SquaresInputs
import Certificates.Kernel.Misc.RuSq.Fix
import Certificates.Kernel.Misc.RuSq.Bind
import CFSG.Certificates.Kernel.Misc.RuSqSound

public section

namespace Certificates

open CertificateChecks

theorem certificate24360 : CFSG.EvenSporadicStandard.TwoRu.ruSquareCheck = true :=
  CFSG.KC.Misc.RuSq.fix2K_sound KernelMisc.RuSq.bindsSq KernelMisc.RuSq.permS
    KernelMisc.RuSqS.hl KernelMisc.RuSq.fixOK

end Certificates

end
