module

public import Certificates.Certificate7006

public section

namespace CFSG.Walter.Ree.Bombieri

namespace Spec

theorem batch9_1_sound :
    ∀ e ∈ batch9_1, Elim.Hs e.k e.lam e.neg ≠ 0 :=
  Certificates.certificate7006

end Spec

end CFSG.Walter.Ree.Bombieri
