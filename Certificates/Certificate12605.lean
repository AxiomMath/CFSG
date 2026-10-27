
module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4CentralizerH11Data
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4CentralizerH11Data
import Certificates.Kernel.SporSch.J4S.H11P
public meta import CFSG.Sporadic.Schreier.J4SCommGenBase
public import CFSG.Sporadic.Schreier.J4SCommGenBase
public meta import CFSG.Sporadic.Schreier.J4SPrimes
public import CFSG.Sporadic.Schreier.J4SPrimes
public import CFSG.Sporadic.Schreier.J4SThreeDataInputs
public meta import CFSG.Sporadic.Schreier.J4SThreeDataInputs

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native in
theorem certificate12605 : (h11B = h11Poly 1 ∧ comp11 h11B h11Binv = idRows 11 ∧ Bounded h11B ∧
      Bounded h11Binv)
    ∧ (∀ w < 2048, Bounded (h11Poly w))
    ∧ (∀ w < 2048, powCols (h11X w) 1024 = h11X w)
    ∧ (∀ w < 2048, powCols (h11X w) 3 = idRows 11 →
      h11X w = idRows 11 ∨ CFSG.Sporadic.J4Schreier.fixCount (h11X w) < 4)
    ∧ (∀ k < 27, 0 < k → 4 ≤ CFSG.Sporadic.J4Schreier.fixCount q3Cols[k]!)
    ∧ (Bounded (idRows 11)) := KernelSporSch.J4H11.facts

end Certificates
