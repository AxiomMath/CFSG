module

public import Certificates.Kernel.Cert690.GlueP
public import Certificates.Kernel.Cert690.GlueM

public section

namespace Certificates

open CertificateChecks

theorem certificate690004 : CFSG.GF2Type.Smith1979W3.Cert690.censusBase false () = true ∧
    CFSG.GF2Type.Smith1979W3.Cert690.censusBase true () = true :=
  ⟨KernelC690.GrpP.censusBaseP, KernelC690.GrpM.censusBaseM⟩

end Certificates
