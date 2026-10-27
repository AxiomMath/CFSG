
module


public import CFSG.Sporadic.Co1.Module.OddCentCardInputs
import Certificates.Kernel.Co1M.C10072

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co1.Module.Odd CFSG.Sporadic.Co1.OddCentNative in
theorem certificate10072 :
    ∃ T : VTree, centOK T = true := KernelCo1M.c10072

end Certificates
