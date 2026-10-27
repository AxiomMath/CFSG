module

public import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeTrialityCheck
import Certificates.Kernel.OmegaEight.T3KGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Curtis.Coordinator in
theorem certificate133001 : triCheck triData = true := KernelO8.T3K.triCheck_true

end Certificates
