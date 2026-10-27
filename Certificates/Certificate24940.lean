module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuFiveInputs
import Certificates.Kernel.Misc.RuFive.LinesFacts

public section

namespace Certificates

open CertificateChecks

theorem certificate24940 : CFSG.EvenSporadicStandard.RuStd.S2.ruFiveLinesCheck = true := KernelMisc.RuFive.lines

end Certificates
