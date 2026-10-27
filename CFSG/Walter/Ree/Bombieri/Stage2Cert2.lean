module

public import Certificates.Certificate7007

public section

namespace CFSG.Walter.Ree.Bombieri

namespace Spec

theorem batch9_2_sound :
    ∀ e ∈ batch9_2, Elim.Hs e.k e.lam e.neg ≠ 0 :=
  Certificates.certificate7007

end Spec

end CFSG.Walter.Ree.Bombieri
