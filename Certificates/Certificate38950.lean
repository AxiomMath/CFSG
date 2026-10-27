module

public import CFSG.Sporadic.Co1.Module.LeechOddChecksInputs
import Certificates.Kernel.Co1N4Spin.Fact

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.Co1.Module.Odd in
open scoped Matrix in
theorem certificate38950 : ∀ U : Submodule (ZMod 2) (Fin 24 → ZMod 2), toVecD 24 code4 ∈ U →
    (∀ u ∈ U, rowsMatrix 24 (rr 23) *ᵥ u ∈ U) → (∀ u ∈ U, rowsMatrix 24 (rr 17) *ᵥ u ∈ U) →
    ∀ y ∈ U, y ∉ Submodule.span (ZMod 2) {toVecD 24 code4} →
    ∃ u ∈ U, u ≠ toVecD 24 code4 ∧ ∃ x < 2 ^ 24, toVecD 24 x = u ∧ isT2 x = true := KernelCo1N4Spin.spinFact

end Certificates
