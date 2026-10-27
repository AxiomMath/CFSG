module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.ECoreInputs
import Certificates.Kernel.Co1Cover.Bridge24530
public import CFSG.Sporadic.Co1.Module.InvDataInputs

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoCo1 CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.Module in
theorem certificate24530 :
    (orderIs eRowsA 2 = true)
    ∧ (countsOK eRowsA 65536 30720 = true)
    ∧ (orderIs eRowsC 2 = true)
    ∧ (countsOK eRowsC 4096 2048 = true) := KernelCo1Cover.ECore.facts24530

end Certificates
