module

public import Certificates.Certificate7000

public section

namespace CFSG.Walter.Ree.Bombieri

theorem appOK_3_69 : ∀ k, 3 ≤ k → k ≤ 69 → k % 2 = 1 → AppOK k :=
  Certificates.certificate7000

end CFSG.Walter.Ree.Bombieri
