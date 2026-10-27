module

public import Certificates.Certificate7003

public section

namespace CFSG.Walter.Ree.Bombieri

theorem appOK_89_91 :
    ∀ k, 89 ≤ k → k ≤ 91 → k % 2 = 1 → AppOK k :=
  Certificates.certificate7003

end CFSG.Walter.Ree.Bombieri
