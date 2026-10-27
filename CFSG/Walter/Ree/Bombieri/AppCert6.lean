module

public import Certificates.Certificate7005

public section

namespace CFSG.Walter.Ree.Bombieri

theorem appOK_99_99 :
    ∀ k, 99 ≤ k → k ≤ 99 → k % 2 = 1 → AppOK k :=
  Certificates.certificate7005

end CFSG.Walter.Ree.Bombieri
