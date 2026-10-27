module

public import Certificates.Certificate7008

public section

namespace CFSG.Walter.Ree.Bombieri

namespace Spec

theorem batch9_3_sound :
    ∀ e ∈ batch9_3, Elim.Hs e.k e.lam e.neg ≠ 0 :=
  Certificates.certificate7008

end Spec

end CFSG.Walter.Ree.Bombieri
