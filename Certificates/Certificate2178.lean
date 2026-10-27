
module

public import Certificates.Certificate2178Base

public import CFSG.Sporadic.Schreier.J4SPrimes
public meta import CFSG.Sporadic.Schreier.J4SPrimes
import Certificates.Kernel.SporSch.J4S.Primes

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native in
theorem certificate2178 : (powCols (wordCols bWord) 48964608 = q5Cols)
    ∧ (powCols q5Cols 5 = idRows 11 ∧ q5Cols ≠ idRows 11 ∧ CFSG.Sporadic.J4Schreier.fixCount q5Cols = 8 ∧
      Bounded q5Cols
    )
    ∧ (powCols (wordCols w7) 2 = q7Cols)
    ∧ (powCols q7Cols 7 = idRows 11 ∧ q7Cols ≠ idRows 11 ∧ CFSG.Sporadic.J4Schreier.fixCount q7Cols = 4 ∧
      Bounded q7Cols
    )
    ∧ (powCols (wordCols w23) 10644480 = q23Cols)
    ∧ (powCols q23Cols 23 = idRows 11 ∧ q23Cols ≠ idRows 11 ∧ Bounded q23Cols)
    ∧ (B23 = polyCols 1 ∧ comp11 B23 B23inv = idRows 11 ∧ Bounded B23 ∧
      Bounded B23inv
    )
    ∧ (∀ w < 2048, Bounded (polyCols w))
    ∧ (∀ w < 2048, powCols (comp11 (polyCols w) B23inv) 11 = idRows 11 → w = 1)
    ∧ (Bounded (idRows 11)) := KernelSporSch.J4Primes.facts

end Certificates
