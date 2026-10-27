module

public import Certificates.Certificate6016

public section

namespace CFSG.Monster.AxisCount.HS

theorem rec_ok_6 :
    ∀ s ∈ recShard_6, ∀ r, s.2.1 ≤ r → r < s.2.2 → ∀ ε, RecSpec s.1 r ε :=
  Certificates.certificate6016

end CFSG.Monster.AxisCount.HS
