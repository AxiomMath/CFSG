module

public import Certificates.Certificate7002

public section

namespace CFSG.Walter.Ree.Bombieri

theorem appOK_81_87 :
    ∀ k, 81 ≤ k → k ≤ 87 → k % 2 = 1 → AppOK k :=
  Certificates.certificate7002

end CFSG.Walter.Ree.Bombieri
