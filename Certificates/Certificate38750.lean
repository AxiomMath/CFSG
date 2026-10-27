module

public import Certificates.Data.SmithD6IdQa
import Certificates.Kernel.SmithD6Id.Facts
import Certificates.Kernel.SmithD6Pinned.Holds

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.SmithD6Pinned

theorem certificate38750 : CFSG.SmithD6.id7ChkQa = true :=
  SmithD6Id.id7ChkQa_of_pinned pinnedModel.lineIdx_of_memB pinnedModel.wt_get
    pinnedModel.wtIdx_lt_iff_memB

end Certificates
