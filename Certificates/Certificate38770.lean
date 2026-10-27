module

public import Certificates.Data.SmithD6Facts
import Certificates.Kernel.SmithD6Adj.Glue
import Certificates.Kernel.SmithD6Pinned.Holds

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.SmithD6Pinned

theorem certificate38770 : CFSG.SmithD6.mf7ChkWt () = true ∧ CFSG.SmithD6.mf7ChkTvAdj0 () = true :=
  ⟨SmithD6Adj.mf7ChkWt_of_pinned pinnedModel.wt_get pinnedModel.wtIdx_lt_iff_memB,
    SmithD6Adj.mf7ChkTvAdj0_of_pinned pinnedModel.wt_get pinnedModel.wtIdx_lt_iff_memB
      pinnedModel.lineKeys_toList⟩

end Certificates
