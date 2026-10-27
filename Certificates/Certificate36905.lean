module

public import Certificates.Data.HNG3Order
public meta import Certificates.Data.HNG3Order
import Certificates.Kernel.SporSch.HN.G3

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.HNSchreier.Native in
theorem certificate36905 : CFSG.HardMathSupport.Solomon.Coordinator.HN3.g3OrderChecks rowsA rowsB = true :=
  KernelSporSch.HNG3.g3_ok

end Certificates
