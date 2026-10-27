module

public import Certificates.Certificate7009

public section

namespace CFSG.Walter.Ree.Bombieri

namespace Spec

theorem batch9_4_sound :
    ∀ e ∈ batch9_4, Elim.Hs e.k e.lam e.neg ≠ 0 :=
  Certificates.certificate7009

end Spec

end CFSG.Walter.Ree.Bombieri
