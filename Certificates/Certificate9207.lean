module

public import Certificates.Certificate9113
public import Certificates.Kernel.Sporadic.Fi24Br.Img

public section

namespace Certificates

open CertificateChecks

open TauCeti in
theorem certificate9207 : ∃ x : ℕ → GL (Fin 781) (ZMod 3),
    (∀ k < 11, (x k : Matrix (Fin 781) (Fin 781) (ZMod 3)) = CFSG.KD.Fi24Img.img k) ∧
    (∀ k, 11 ≤ k → x k = 1) ∧
    (∀ v ∈ Sporadic.fi24PrimePresentation.relatorLetters, CFSG.Sporadic.Bridge.wordProd x v = 1) ∧
    ∀ g : GL (Fin 781) (ZMod 3),
      g.val = CFSG.Blueprint.NativeSporadic.decode 3 781 1
          CFSG.Blueprint.NativeSporadic.Fi24primeSeed1 ∨
        g.val = CFSG.Blueprint.NativeSporadic.decode 3 781 1
          CFSG.Blueprint.NativeSporadic.Fi24primeSeed2 →
      g ∈ Subgroup.closure (x '' Set.Iio 11) := KernelSpor.Fi24Img.bridge_x

end Certificates
