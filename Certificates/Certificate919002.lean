module

public import Certificates.Data.Foote82OmegaSix

public section

open CFSG.CGT.Foote82.OmegaSix

namespace CertificateChecks.Batch919002

open CFSG.CGT.Foote82.OmegaSix

set_option maxHeartbeats 0 in
private theorem foxCheck_holds : foxCheck () = true := by
  decide +kernel

end CertificateChecks.Batch919002

namespace Certificates

open CertificateChecks

open CFSG.CGT.Foote82.OmegaSix in
theorem certificate919002 : foxCheck () = true :=
  CertificateChecks.Batch919002.foxCheck_holds

end Certificates
