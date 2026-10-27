module

public import CFSG.HardMathSupport.Foote.E27.LieTwo.SpModel
import Certificates.Kernel.E27Orth.Sp8Glue

public section

namespace Certificates

open CFSG.HardMathSupport.Foote.E27 in
theorem certificate131003 : ∃ S B : Subgroup (SpJ 4), Nat.card S = 3 ^ 5 ∧ Nat.card B = 3 ^ 4 ∧
    (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧
    (∀ s ∈ S, s ^ 3 = 1 → s ≠ 1 → ∃ x : SpJ 4, x * s * x⁻¹ ∈ B) :=
  CertificateChecks.KernelE27Orth.Sp8.sp8131003_fact

end Certificates
