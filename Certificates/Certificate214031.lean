module

public import Certificates.Data.SuzPairSize
public meta import Certificates.Data.SuzPairSize
import Certificates.Kernel.SuzPump.PairFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Solomon.Coordinator.SuzPump in
theorem certificate214031 : pairEqCheck () = true := KernelSuzPump.pair_ok

end Certificates
