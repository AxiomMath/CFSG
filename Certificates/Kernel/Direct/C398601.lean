module

public import Certificates.Data.TwinPerpV3A6dNoFive
import all Certificates.Data.TwinPerpV3A6dNoFive

public section

namespace CertificateChecks.KernelDirect.C398601

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6d

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem noFiveCheck_eq_true : noFiveCheck () = true := by
  decide +kernel

end CertificateChecks.KernelDirect.C398601
