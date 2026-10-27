module

public import Certificates.Data.SmithD6Tr7
import Certificates.Kernel.SmithD6Tr7.Facts
import Certificates.Kernel.SmithD6Pinned.Holds

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.SmithD6Pinned

theorem certificate38791 : CFSG.SmithD6.tr7ChkDims = true :=
  SmithD6Tr7.tr7ChkDims_of_pinned pinnedModel.lineIdx_of_memB pinnedModel.wtArr_toList

end Certificates
