module

public import CFSG.Sporadic.J4.QTOutActNative
import Certificates.Kernel.J4Q.C4018

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT in
theorem certificate4018 : (orbits.length = 2 ∧ (orbits.getD 0 (0, [], [])).1 = 1 ∧
          (orbits.getD 1 (0, [], [])).1 = 3)
    ∧ (o1.length = 276 ∧ o1.Nodup)
    ∧ (o2.length = 1771 ∧ o2.Nodup)
    ∧ (∀ c ∈ o1 ++ o2, c < 2 ^ 11 ∧ c ≠ 0)
    ∧ (∀ c < 2 ^ 11, c ≠ 0 → c ∈ o1 ∨ c ∈ o2)
    ∧ (∀ c ∈ o1, c ∉ o2)
    ∧ (1 ∈ o1 ∧ 3 ∈ o2)
    ∧ ((∀ c ∈ o1, ∀ ℓ ∈ letters, act ℓ c ∈ o1) ∧ ∀ c ∈ o2, ∀ ℓ ∈ letters, act ℓ c ∈ o2)
    ∧ (∀ c < 2 ^ 11, actT (tp 23) c = c)
    ∧ (∀ n < 23, lenOK (tp n) = true)
    ∧ (∀ c < 2 ^ 11, kcomb (kinv.getD c 0) = c ∧ kinv.getD c 0 < 2 ^ 11)
    ∧ (∀ ℓ ∈ hWord, ℓ ∈ letters)
    ∧ (∀ s < 23, s ≠ 0 → ∀ w ∈ o1, survOK s w = true → survIn s w = true) := KernelJ4Q.c4018

end Certificates
