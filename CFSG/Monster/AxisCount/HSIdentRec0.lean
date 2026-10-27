module

public import Certificates.Certificate6010

public section

namespace CFSG.Monster.AxisCount.HS

theorem rec_ok_0 :
    ∀ s ∈ recShard_0, ∀ r, s.2.1 ≤ r → r < s.2.2 → ∀ ε, RecSpec s.1 r ε :=
  Certificates.certificate6010

end CFSG.Monster.AxisCount.HS
