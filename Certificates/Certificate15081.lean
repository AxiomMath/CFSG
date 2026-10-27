module

public import Certificates.Data.GMS78RuCheck
import Certificates.Kernel.GMS78.C

public section

namespace Certificates

open CertificateChecks

theorem certificate15081 : CFSG.GMS78Ru.c1Check = true ∧ CFSG.GMS78Ru.c2Check = true ∧
    CFSG.GMS78Ru.c3Check = true :=
  ⟨KernelGMS78.c1Check_eq, KernelGMS78.c2Check_eq, KernelGMS78.c3Check_eq⟩

end Certificates
