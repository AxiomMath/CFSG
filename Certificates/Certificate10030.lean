module

public import CFSG.Monster.GMS.EdgeSqCo1Inputs
import Certificates.Kernel.Co1M.C10030
public import CFSG.Sporadic.Co1.Module.InvDataInputs

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.GMS.EdgeSq CFSG.Sporadic.Co1.Module in
theorem certificate10030 :
    (edgeCheck rowsSA = true)
    ∧ (edgeCheck rowsSC = true) := KernelCo1M.c10030

end Certificates
