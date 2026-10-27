module

public import Certificates.Data.SmithL6RhoCheck
import CFSG.Certificates.Kernel.SmithL6RankSound
import Certificates.Kernel.SmithL6Rank.Checks

public section

namespace Certificates

open CertificateChecks

theorem certificate38602 : CFSG.SmithL6.chkSpanW = true ∧ CFSG.SmithL6.chkRank = true :=
  ⟨CFSG.SmithL6.Kernel.chkSpanW_of_K KernelSmithL6Rank.spanK,
    CFSG.SmithL6.Kernel.chkRank_of_K KernelSmithL6Rank.rankK⟩

end Certificates
