module

public import Certificates.Kernel.SmithEK.ChkR

public section

namespace Certificates

theorem certificate21261 :
    CFSG.SmithE.chkSpanW = true ∧ CFSG.SmithE.chkDist = true ∧ CFSG.SmithE.chkRank = true :=
  ⟨CertificateChecks.KernelSmithEK.chkSpanW_eq, CertificateChecks.KernelSmithEK.chkDist_eq,
    CertificateChecks.KernelSmithEK.chkRank_eq⟩

end Certificates
