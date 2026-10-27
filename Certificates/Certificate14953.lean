module

public import CFSG.SignalizerFunctorTheorem.NonLocalExc.U33SmallIndexInputs
import Certificates.Kernel.Misc.Perm.U33B.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.SignalizerFunctorTheorem.NonLocalExc in
theorem certificate14953 : Nat.card Bsub = 216 ∧
    (∀ x ∈ Bsub, ∀ y ∈ Bsub, x ^ 3 = 1 → y ^ 3 = 1 → (x * y) ^ 3 = 1) ∧
    Nat.card {g // g ∈ Bsub ∧ g ^ 3 = 1} = 27 ∧
    ∃ z ∈ Bsub, z ^ 3 = 1 ∧ z ≠ 1 ∧
      (∃ x ∈ Bsub, ∃ y ∈ Bsub, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ z = x * y * x⁻¹ * y⁻¹) ∧
      ∀ a ∈ Bsub, a ^ 3 = 1 → a ≠ 1 → a ≠ z → a⁻¹ ≠ z →
        Nat.card {x // x ∈ Bsub ∧ ¬ x ^ 3 = 1 ∧ (x * a * x⁻¹ = a ∨ x * a * x⁻¹ = a⁻¹)} ≤ 11 := KernelMisc.U33B.facts

end Certificates
