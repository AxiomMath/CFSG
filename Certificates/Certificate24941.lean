module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuFiveInputs
import Certificates.Kernel.Misc.RuFive.Q8Facts

public section

namespace Certificates

open CertificateChecks

theorem certificate24941 : CFSG.EvenSporadicStandard.RuStd.S2.ruFiveQ8Check = true := KernelMisc.RuFive.q8

end Certificates
