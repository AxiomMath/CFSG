module

public import CFSG.Sporadic.HN.LocalK
import Certificates.Kernel.HNLocal.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.F5 CFSG.Sporadic.HN.LocalK in
theorem certificate6099 : wG 12 • rootV = rootV ∧ wG 13 • rootV = rootV ∧
    (∀ k, wG 12 • hnW k = hnW (pit2 k)) ∧ (∀ k, wG 13 • hnW k = hnW (pit4 k)) ∧ wG 14 = wG 2 ∧
    ∃ X : Fin 1140000 → Vec dHN, Function.Injective X ∧
      (∀ k, X k ∈ MulAction.orbit (J dHN) rootV) ∧
      Nat.card {k // wG 12 • X k = X k} = 8800 ∧ Nat.card {k // wG 13 • X k = X k} = 800 := KernelHNLocal.facts6099

end Certificates
