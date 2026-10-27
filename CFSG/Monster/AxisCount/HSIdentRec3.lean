module

public import Certificates.Certificate6013

public section

namespace CFSG.Monster.AxisCount.HS

theorem rec_ok_3 :
    ∀ s ∈ recShard_3, ∀ r, s.2.1 ≤ r → r < s.2.2 → ∀ ε, RecSpec s.1 r ε :=
  Certificates.certificate6013

end CFSG.Monster.AxisCount.HS
