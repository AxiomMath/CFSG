
module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Certificates.Kernel.SolMax.SixGenF

public section

namespace Certificates

open CertificateChecks

open Equiv Subgroup in
theorem certificate22257 : ∀ {u v : Perm (Fin 9)}, u * u = 1 → v * v = 1 → u * v = v * u → u.support.card = 6 →
    alternatingGroup (Fin 9) ≤ (centralizer {u} ⊓ alternatingGroup (Fin 9)) ⊔
      (centralizer {v} ⊓ alternatingGroup (Fin 9)) ⊔
      (centralizer {u * v} ⊓ alternatingGroup (Fin 9)) :=
  KernelSolMax.SixGen.fact22257

end Certificates
