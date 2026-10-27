module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.ECoreInputs
public import CFSG.Sporadic.Co1Block.XFix
public import CFSG.Sporadic.Co1Block.PermData
public meta import CFSG.Sporadic.Co1Block.XFix
public meta import CFSG.Sporadic.Co1Block.PermData
import Certificates.Kernel.Co1B.C24531
public import CFSG.Sporadic.Co1.Module.InvDataBase
public import CFSG.Sporadic.Co1.Module.InvRepsBase

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoCo1 CFSG.Sporadic.Co1Block in
theorem certificate24531 :
    (xFixCount certVecs eRowsA = 2280)
    ∧ (xFixCount certVecs eRowsC = 264) := KernelCo1B.C24531.c24531

end Certificates
