module

public import Certificates.Data.Co3Pump
public meta import Certificates.Data.Co3Pump
import Certificates.Kernel.Co3Pump36903.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Solomon.Coordinator.Co3Pump in
theorem certificate36903 : fuseCheck () = true ∧ pairACheck () = true ∧ pairBCheck () = true ∧
    fiveCheck () = true :=
  KernelCo3Pump36903.facts

end Certificates
