module

public import Certificates.Certificate9109

public section

namespace CFSG.Sporadic.Presentation.Fi22Exact

theorem six_dvd_orderOf_g1 :
    6 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 6) | r ∈ wsF.map FreeGroup.mk}
      (FreeGroup.mk g1w)) :=
  Certificates.certificate9109

end CFSG.Sporadic.Presentation.Fi22Exact
