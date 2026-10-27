module

public import CFSG.Sporadic.Co1Patterson.AmalgamRigidInputs
import Certificates.Kernel.Co1P.C21158

public section

namespace Certificates

open CertificateChecks

theorem certificate21158 : CFSG.Sporadic.Co1Patterson.Native.qaeOK = true ∧
    CFSG.Sporadic.Co1Patterson.Native.edgeElemOK = true ∧
    CFSG.Sporadic.Co1Patterson.Native.stabOK = true ∧
    CFSG.Sporadic.Co1Patterson.Native.perpOK = true := KernelCo1P.c21158

end Certificates
