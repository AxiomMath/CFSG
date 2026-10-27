module

public import Certificates.Data.TabMThreeAFi24
public import Certificates.Data.Kernel.Spor.Fi24Img
public import CFSG.Sporadic.Bridge.Common
import Certificates.Kernel.Sporadic.Fi24KM.Words

public section

namespace Certificates

open CertificateChecks

theorem certificate17593 : ∀ x : ℕ → GL (Fin 781) (ZMod 3),
    (∀ k < 11, (x k : Matrix (Fin 781) (Fin 781) (ZMod 3)) = CFSG.KD.Fi24Img.img k) →
    (∀ v ∈ CFSG.HardMathSupport.Dickson.I271.TabMThreeA.kmRels (),
      CFSG.Sporadic.Bridge.wordProd x v = 1) ∧
    ∀ v ∈ CFSG.HardMathSupport.Dickson.I271.TabMThreeA.kmMoves (),
      CFSG.Sporadic.Bridge.wordProd x v ≠ 1 := KernelSpor.Fi24KM.km_words

end Certificates
