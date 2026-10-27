module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.LyThirtyOneCheck
import Certificates.Kernel.Misc.Ly31Facts

public section

namespace Certificates

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic in
theorem certificate1322151 : ly31Check () = true :=
  CertificateChecks.KernelLy31.ly31Check_true

end Certificates
