module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.LyCheck
import Certificates.Kernel.Misc.LyDihFacts

public section

namespace Certificates

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic in
theorem certificate129001 : lyDihCheck () = true :=
  CertificateChecks.KernelLyDih.lyDihCheck_true

end Certificates
