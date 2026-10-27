module

public import Certificates.Certificate7004

public section

namespace CFSG.Walter.Ree.Bombieri

theorem appOK_93_97 :
    ∀ k, 93 ≤ k → k ≤ 97 → k % 2 = 1 → AppOK k :=
  Certificates.certificate7004

end CFSG.Walter.Ree.Bombieri
