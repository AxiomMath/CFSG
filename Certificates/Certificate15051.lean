module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowQETests
import Certificates.Kernel.LocalComp.HeSylowQECheck

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15051 : CFSG.ComponentClassification.AS81.HeSylow.heSylowQECheck = true :=
  KernelLC.HeSylowQECheck.heSylowQECheck_true

end Certificates
