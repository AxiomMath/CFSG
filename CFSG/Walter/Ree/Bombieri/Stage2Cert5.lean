module

public import Certificates.Certificate7010

public section

namespace CFSG.Walter.Ree.Bombieri

namespace Spec

theorem batch9_5_sound :
    ∀ e ∈ batch9_5, Elim.Hs e.k e.lam e.neg ≠ 0 :=
  Certificates.certificate7010

end Spec

end CFSG.Walter.Ree.Bombieri
