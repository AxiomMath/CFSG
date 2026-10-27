module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3A6Data
import Certificates.Kernel.A6Ord.Checks
import Certificates.Kernel.ONanA6.Checks
import Certificates.Kernel.ONanA6.Codes
import CFSG.Certificates.Kernel.A6OrdSound

namespace Certificates

theorem la_mem_26081 (x : CFSG.QuasithinUnique.A6Facts.P10)
    (hx : x ∈ CFSG.QuasithinUnique.A6Models.autA6) : CFSG.KC.LQT.P.code x ∈ CFSG.KD.ONanA6.la :=
  CFSG.KC.ONanA6.mem_la CFSG.KD.ONanA6.hl CFSG.KD.ONanA6.hr
    ((CFSG.KC.LQT.S.eqLs_iff _ _).1 CFSG.KD.ONanA6.hAut) hx

end Certificates

public section

namespace Certificates

theorem certificate26081 : CFSG.EvenSporadicStandard.Fin76b.A6OrdData :=
  CFSG.KC.A6Ord.a6OrdData_of la_mem_26081 CertificateChecks.KernelA6Ord.ch26081

end Certificates
