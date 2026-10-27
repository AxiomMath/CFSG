module

public import Certificates.Certificate6099

public section

namespace CFSG.Sporadic.HN.Local

open CFSG.Sporadic.F5 CFSG.Sporadic.HN.LocalK

theorem type_certificate :
    wG 12 • rootV = rootV ∧ wG 13 • rootV = rootV ∧
      (∀ k, wG 12 • hnW k = hnW (pit2 k)) ∧ (∀ k, wG 13 • hnW k = hnW (pit4 k)) ∧ wG 14 = wG 2 ∧
      ∃ X : Fin 1140000 → Vec dHN, Function.Injective X ∧
        (∀ k, X k ∈ MulAction.orbit (J dHN) rootV) ∧
        Nat.card {k // wG 12 • X k = X k} = 8800 ∧ Nat.card {k // wG 13 • X k = X k} = 800 :=
  Certificates.certificate6099

end CFSG.Sporadic.HN.Local
