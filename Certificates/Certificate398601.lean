module

public import Certificates.Data.TwinPerpV3A6dNoFive
import Certificates.Kernel.Direct.C398601

public section

namespace Certificates

open CertificateChecks

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6d in
theorem certificate398601 : noFiveCheck () = true :=
  KernelDirect.C398601.noFiveCheck_eq_true

end Certificates
