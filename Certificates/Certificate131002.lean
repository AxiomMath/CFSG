module

public import CFSG.HardMathSupport.Foote.E27.LieTwo.SpModel
import Certificates.Kernel.E27Orth.Sp6Glue

public section

namespace Certificates

open Subgroup Matrix CFSG.HardMathSupport.Foote.E27 in
theorem certificate131002 : ∃ S : Subgroup (SpJ 3), Nat.card S = 3 ^ 4 ∧
    (∀ c ∈ S, c ≠ 1 → (∀ s ∈ S, s * c = c * s) →
      ∀ v : Fin (3 + 3) → ZMod 2, matJ 3 c *ᵥ v = v → v = 0) ∧
    (∀ a ∈ S, ∀ b ∈ S, a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a → a ≠ 1 → b ∉ zpowers a →
      ∃ i j : ℕ, a ^ i * b ^ j ≠ 1 ∧
        ¬ ∀ v : Fin (3 + 3) → ZMod 2, matJ 3 (a ^ i * b ^ j) *ᵥ v = v → v = 0) :=
  CertificateChecks.KernelE27Orth.Sp6.sp6131002_fact

end Certificates
