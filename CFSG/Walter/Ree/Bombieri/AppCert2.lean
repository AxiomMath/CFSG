module

public import Certificates.Certificate7001

public section

namespace CFSG.Walter.Ree.Bombieri

theorem appOK_71_79 :
    ∀ k, 71 ≤ k → k ≤ 79 → k % 2 = 1 → AppOK k :=
  Certificates.certificate7001

end CFSG.Walter.Ree.Bombieri
