module

public import Certificates.Kernel.SmithL6K.GlueS

public section

namespace Certificates

open CertificateChecks

theorem certificate38652 : CFSG.SmithL6.mfChkPair0 = true ∧ CFSG.SmithL6.mfChkSpan = true ∧
    CFSG.SmithL6.mfChkInt0 = true :=
  ⟨KernelSmithL6K.mfChkPair0_holds, KernelSmithL6K.mfChkSpan_holds,
    KernelSmithL6K.mfChkInt0_holds⟩

end Certificates
