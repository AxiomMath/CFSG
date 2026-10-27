module

public import Certificates.Kernel.Cert690.CensSMGoal

public section

namespace Certificates

open CertificateChecks

theorem certificate690006 : ∀ j < (CFSG.GF2Type.Smith1979W3.Cert690.candidatesOf true
      (CFSG.GF2Type.Smith1979W3.Cert690.ldata true ()).Llist).size,
    CFSG.GF2Type.Smith1979W3.Cert690.CensusLGoal true j :=
  KernelC690.CensSM.censusLGoalM

end Certificates
