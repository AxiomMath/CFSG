module

public import Certificates.Data.SmithL6E23a
import Certificates.Kernel.SmithL6K.GlueEa

public section

namespace Certificates

open CertificateChecks

theorem certificate38671 : CFSG.SmithL6.eaChkC8 = true ∧ CFSG.SmithL6.eaChkW = true ∧
    CFSG.SmithL6.eaChkF4 = true ∧ CFSG.SmithL6.eaChkRig = true :=
  ⟨KernelSmithL6K.eaC8_holds, KernelSmithL6K.eaW_holds, KernelSmithL6K.eaF4_holds,
    KernelSmithL6K.eaRig_holds⟩

end Certificates
