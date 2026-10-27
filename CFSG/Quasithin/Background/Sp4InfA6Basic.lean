
module


public import Certificates.Certificate8066

public section

namespace CFSG.Quasithin

namespace Sp4Inf

open Equiv Pointwise

theorem card_s0 : Nat.card s0 = 8 :=
  Certificates.certificate8066.2.2.1

theorem card_alt_six' : Nat.card (alternatingGroup (Fin 6)) = 360 :=
  Certificates.certificate8066.2.2.2.1

theorem fix_of_normalizes_s0 :
    ∀ g : Perm (Fin 6), (∀ x, bs0 x = true → bs0 (g * x * g⁻¹) = true) →
      (∀ x, bq1 x = true → bq1 (g * x * g⁻¹) = true) ∧
        ∀ x, bq2 x = true → bq2 (g * x * g⁻¹) = true :=
  Certificates.certificate8066.2.2.2.2

end Sp4Inf

end CFSG.Quasithin
