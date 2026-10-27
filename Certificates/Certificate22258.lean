module

public import Certificates.Data.SolMaxNineE32

public section

open CFSG.ComponentClassification.SolMax.NineE32

namespace CertificateChecks.Batch22258

open CFSG.ComponentClassification.SolMax.NineE32

set_option maxHeartbeats 0 in
private theorem nine_e32_0 : check () = true := by
  decide +kernel

end CertificateChecks.Batch22258

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.SolMax.NineE32 in
theorem certificate22258 : check () = true := by
  exact CertificateChecks.Batch22258.nine_e32_0

end Certificates
