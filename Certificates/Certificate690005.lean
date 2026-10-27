module

public import Certificates.Kernel.Cert690.CensSPGoal

public section

namespace Certificates

open CertificateChecks

theorem certificate690005 : ∀ j < (CFSG.GF2Type.Smith1979W3.Cert690.candidatesOf false
      (CFSG.GF2Type.Smith1979W3.Cert690.ldata false ()).Llist).size,
    CFSG.GF2Type.Smith1979W3.Cert690.CensusLGoal false j :=
  KernelC690.CensSP.censusLGoalP

end Certificates
