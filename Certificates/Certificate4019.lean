module

public import CFSG.Sporadic.J4.QTOutNative
import Certificates.Kernel.J4Q.C4019

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT in
theorem certificate4019 : (∀ L ∈ ucsMasks, ∀ c ∈ L, c < 2 ^ 11)
    ∧ (ucsMasks.getD 0 [] = [0])
    ∧ (ucsMasks.length = 5)
    ∧ (∀ k < 4, ucsStep (ucsMasks.getD k []) (ucsMasks.getD (k + 1) []) = true)
    ∧ (∀ t ∈ tabL, fixesZ4 t = true → t = idT ∨ t = tET)
    ∧ (tET ∈ tabL ∧ compT tET tET = idT ∧ tET ≠ idT)
    ∧ (fixesZ4 tET = true)
    ∧ (eT < 1024) := KernelJ4Q.c4019

end Certificates
