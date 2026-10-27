module

public import Certificates.Data.SmithD6IdCv
import Certificates.Kernel.SmithD6Id.Facts
import Certificates.Kernel.SmithD6Pinned.Holds

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.SmithD6Pinned

theorem certificate38751 : CFSG.SmithD6.id7ChkCv = true :=
  SmithD6Id.id7ChkCv_of_pinned pinnedModel.lineIdx_of_memB
    (by
      obtain ⟨h, h1⟩ := SmithD6Id.wt0_pinned
      rw [pinnedModel.wt_get 0 h, h1])

end Certificates
