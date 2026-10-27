module

public import Certificates.Kernel.SmithEK.ChkI

public section

namespace Certificates

theorem certificate21107 :
    CFSG.SmithE.chkSpan = true ∧ CFSG.SmithE.chkI = true :=
  ⟨CertificateChecks.KernelSmithEK.chkSpan_eq_true, CertificateChecks.KernelSmithEK.chkI_eq_true⟩

end Certificates
