module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.HNCheck
import Certificates.Kernel.Misc.HNHeisFacts

public section

namespace Certificates

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic in
theorem certificate129008 : hnHeisCheck () = true :=
  CertificateChecks.KernelHNHeis.hnHeisCheck_true

end Certificates
