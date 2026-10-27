module

public import Certificates.Data.Co2Pump
public meta import Certificates.Data.Co2Pump
import Certificates.Kernel.Co2Pump.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Solomon.Coordinator.Co2Pump in
theorem certificate36904 : fuseCheck () = true ∧ pairACheck () = true ∧ pairBCheck () = true ∧
    fiveCheck () = true := KernelCo2Pump.ok36904

end Certificates
