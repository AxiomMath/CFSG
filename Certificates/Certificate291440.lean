module

public import CFSG.Sporadic.ON.Chain
import Certificates.Kernel.Sporadic.ONVs.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.ON CFSG.Sporadic.ON.Native in
theorem certificate291440 : ∃ f : Fin nPts → Fin 7,
    (∀ p q, f p = f q ↔ ∃ h ∈ lvl 1, h • p = q) ∧
    (∀ i, (Finset.univ.filter (fun p => f p = i)).card =
      ![1, 1, 11172, 117306, 52136, 52136, 12768] i) ∧
    f root = 0 ∧ f ⟨1, by norm_num⟩ = 1 :=
  KernelSpor.ONVs.vs_orbits

end Certificates
