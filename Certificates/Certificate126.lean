module

public import Certificates.Data.E4QuatSp6Link

public section

namespace Certificates

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certificate126 : CFSG.ClassicalInvolution.Q3.TL4.E4Sp6.linkCheck () = true := by
  decide +kernel

end Certificates
