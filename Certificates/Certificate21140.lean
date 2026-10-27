module

public import CFSG.Sporadic.Co1Block.TwoACheckInputs
public import CFSG.Sporadic.Co1Patterson.NativeQInputs
import Certificates.Kernel.Co1B.C21140

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co1Block in
theorem certificate21140 :
    CFSG.Sporadic.Co1Patterson.Native.qExtraOK iotaARows twoAQRows = true := KernelCo1B.c21140

end Certificates
