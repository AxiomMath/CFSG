module

public import Certificates.Certificate7011

public section

namespace CFSG.Walter.Ree.Bombieri

namespace Spec

theorem batch8_sound :
    ∀ e ∈ batch8, Elim.Hs e.k e.lam e.neg ≠ 0 :=
  Certificates.certificate7011.1

theorem batch7_sound :
    ∀ e ∈ batch7, Elim.Hs e.k e.lam e.neg ≠ 0 :=
  Certificates.certificate7011.2

end Spec

end CFSG.Walter.Ree.Bombieri
