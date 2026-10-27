module

public import CFSG.Sporadic.Fi24I301.Facts
import Certificates.Kernel.Sporadic.Fi24F4.JFinal
import Certificates.Kernel.Sporadic.Fi24F4.Forms

public section

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi24I301 in
theorem certificate810307 : (∀ c : Fin 10 → ZMod 3,
      (∀ k : Fin 2, nMat k * altMat c * (nMat k).transpose = altMat c) → c = 0) ∧
    (∀ q : Fin 5 → ZMod 3, (∀ k : Fin 2, (nMat k).mulVec q = q) → q = 0) ∧
    CoverFacts :=
  ⟨KernelSpor.Fi24F4.noAltForm, KernelSpor.Fi24F4.noLinForm, CFSG.KD.Fi24F4.coverFacts_of⟩

end Certificates

end

end
