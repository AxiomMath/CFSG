module

public import Certificates.Certificate6011

public section

namespace CFSG.Monster.AxisCount.HS

theorem rec_ok_1 :
    ∀ s ∈ recShard_1, ∀ r, s.2.1 ≤ r → r < s.2.2 → ∀ ε, RecSpec s.1 r ε :=
  Certificates.certificate6011

end CFSG.Monster.AxisCount.HS
