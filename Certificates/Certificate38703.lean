module

public import Certificates.Data.SmithD6RhoCheck
import Certificates.Kernel.SmithD6Kc.RankFacts
import Certificates.Kernel.SmithD6Pinned.Holds

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.SmithD6Pinned

theorem certificate38703 : CFSG.SmithD6.chkSpanW = true ∧
    CFSG.SmithD6.chkRank = true :=
  ⟨SmithD6Kc.chkSpanW_of_pinned pinnedModel.wt_get,
    SmithD6Kc.chkRank_of_pinned pinnedModel.pbArr_get pinnedModel.ppArr_get⟩

end Certificates
