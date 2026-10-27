module

public import Certificates.Data.SmithD6E23a
import Certificates.Kernel.SmithD6Ea.Glue
import Certificates.Kernel.SmithD6Pinned.Holds

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.SmithD6Pinned

theorem certificate38801 : CFSG.SmithD6.ea7ChkRig = true :=
  SmithD6Ea.ea7ChkRig_of_pinned pinnedModel.lineKeys_toList pinnedModel.lineIdx_of_memB
    pinnedModel.lineKeys_lineIdx

end Certificates
