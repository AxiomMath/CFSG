module

public import Certificates.Data.Co3PairSize
public meta import Certificates.Data.Co3PairSize
import Certificates.Kernel.Co3Pair.Facts
import CFSG.Certificates.Kernel.BfsPinSound

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Solomon.Coordinator.Co3Pump in
theorem certificate214030 : pairASize () = 1215 ∧ pairBSize () = 14580 :=
  ⟨KernelCo3Pair.pairASize_eq, KernelCo3Pair.pairBSize_eq⟩

end Certificates
