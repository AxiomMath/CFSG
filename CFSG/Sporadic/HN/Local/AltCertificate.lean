module

public import Certificates.Certificate6097

public section

namespace CFSG.Sporadic.HN.Local

open CFSG.Sporadic.F5 CFSG.Sporadic.HN.LocalK

theorem alt_certificate :
    wG 2 • rootV = rootV ∧ wG 3 • rootV = rootV ∧ Function.Injective hnW ∧
      (∀ k, wG 2 • hnW k = hnW (pi2 k)) ∧ (∀ k, wG 3 • hnW k = hnW (pi3 k)) ∧
      1140000 ≤ Nat.card (MulAction.orbit (J dHN) rootV) :=
  Certificates.certificate6097

end CFSG.Sporadic.HN.Local
