module

public import Certificates.Data.E4QuatSp6Three

public section

namespace Certificates

set_option maxHeartbeats 0 in
theorem certificate55120 : CFSG.ClassicalInvolution.Q3.TL4.E4Sp6.sp6ThreeCheck () = true := by
  decide +kernel

end Certificates
