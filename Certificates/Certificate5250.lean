module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
import Certificates.Kernel.Ivk8KBNorm.Final

public section

namespace Certificates

open CFSG.ComponentClassification.PSL3Four in
theorem certificate5250 : (∀ x ∈ R, x ≠ 1 → x ^ 3 = 1 → ∃ d ∈ C₁, d * x ≠ x * d) ∧
    (∀ y ∈ R, y ∉ CFSG.ComponentClassification.PSL3Four.S → y ^ 3 = 1 → r₄ * y = y * r₄ → ∃ d ∈ C₄, (y * (d * y * d⁻¹)) ^ 3 ≠ 1) :=
  CFSG.KS.Ivk8KBNorm.Final.cent_fix

end Certificates
