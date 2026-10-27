module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOneBaseInputs
import Certificates.Kernel.Misc.RuBase.C

public section

namespace Certificates

open CertificateChecks

theorem certificate24370 : CFSG.EvenSporadicStandard.TwoRu.HypOne.fourBaseC = true := KernelMisc.RuBase.fourBaseC_true

end Certificates

end
