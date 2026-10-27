module

public import CFSG.Quasithin.H13.AS91Sec4EightSplitInputs
import CFSG.Certificates.Kernel.AS91SplitSound
import Certificates.Kernel.AS91Split.Split

public section

namespace Certificates

open CertificateChecks.KernelAS91Split

open CFSG.Quasithin.H13.AS91 in
theorem certificate89409 : Two.splitOK48 () = true :=
  Certificates.Kernel.AS91Split.splitOK48_of ch89409_s ch89409_core ch89409_u ch89409_cj

end Certificates
