module

public import Certificates.Data.SuzTwoAExtension
import Certificates.Kernel.LocalComp.Tau1379103Proof

public section

namespace Certificates

open CertificateChecks

theorem certificate1379103 : CFSG.ComponentClassification.AS81.SuzB0.tauCheck () = true :=
  KernelLC.Tau1379103.tauCheck_true

end Certificates
