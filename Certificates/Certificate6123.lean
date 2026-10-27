module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
import Certificates.Kernel.Misc.Perm.SylCent.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.PSL3Four in
theorem certificate6123 : ∃ P : Subgroup (Equiv.Perm (Fin 42)), P ≤ CFSG.ComponentClassification.PSL3Four.S ∧ Nat.card P = 64 ∧
    ∀ x ∈ R, (∀ p ∈ P, x * p = p * x) → x ∈ P := KernelMisc.SylCent.facts

end Certificates
