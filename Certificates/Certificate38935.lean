module

public import Certificates.Data.SmithD6Kc
import Certificates.Kernel.SmithD6Kc.Facts
import Certificates.Kernel.SmithD6Pinned.Holds

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.SmithD6Pinned

theorem certificate38935 : CFSG.SmithD6.chkKcMeet = true ∧ CFSG.SmithD6.chkKcThrough = true :=
  ⟨SmithD6Kc.chkKcMeet_of_pinned pinnedModel.pbArr_get pinnedModel.ppArr_get,
    SmithD6Kc.chkKcThrough_of_pinned pinnedModel.pbArr_get pinnedModel.ppArr_get⟩

end Certificates
