module

public import CFSG.Sporadic.J4.QTOutCocNative
public import CFSG.Sporadic.J4.QTRankNative
import Certificates.Kernel.J4Q.C4020

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT in
theorem certificate4020 : (∀ r ∈ rel01 ++ rel02 ++ relMix, wordT r = idT)
    ∧ (∀ r ∈ rel01 ++ rel02 ++ relMix, ∀ ℓ ∈ r, ℓ ∈ letters)
    ∧ (∀ r ∈ rel01, ∀ ℓ ∈ r, ℓ = 1 ∨ ℓ = -1 ∨ ℓ = 2 ∨ ℓ = -2)
    ∧ (∀ r ∈ rel02, ∀ ℓ ∈ r, ℓ = 1 ∨ ℓ = -1 ∨ ℓ = 3 ∨ ℓ = -3)
    ∧ (stage1 = [0, 1373])
    ∧ (stage2 = [0, 689])
    ∧ (relAll 0 0 = true ∧ relAll 1373 689 = true ∧ relAll 0 689 = false ∧
          relAll 1373 0 = false)
    ∧ (∀ e < 2 ^ 11, ∃ v < 2 ^ 11, v ^^^ actT (letterTab 1) v = e) := KernelJ4Q.c4020

end Certificates
