module

public import CFSG.Sporadic.SuzI301Cover.Inputs
import Certificates.Kernel.Sporadic.SuzH.Proof

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SuzI301Cover.Native in
theorem certificate810308 : (∀ C : Matrix (Fin 3) (Fin 3) (ZMod 3), (∀ i, C i i = 0) → (∀ i j, C j i = -C i j) →
      (∀ k : Fin 2, nMat k * C * (nMat k).transpose = C) → C = 0) ∧
    (∀ q : Fin 3 → ZMod 3, (∀ k : Fin 2, (nMat k).mulVec q = q) → q = 0) ∧
    suzhCheck () = true :=
  ⟨KernelSpor.SuzH.alt_zero, KernelSpor.SuzH.fix_zero, KernelSpor.SuzH.suzh_check⟩

end Certificates
