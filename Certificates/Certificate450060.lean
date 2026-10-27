module

public import CFSG.Sporadic.Fi23.Simple
import Certificates.Kernel.U62K.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi23 (lvl) in
theorem certificate450060 : 
    (∀ α : MulAut ↥(CFSG.Sporadic.Fi23.lvl 2), α ≠ 1 → α * α = 1 → ∃ E : Subgroup ↥(CFSG.Sporadic.Fi23.lvl 2), (∀ x ∈ E, α x = x) ∧
      (∀ x ∈ E, x * x = 1) ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ 64 ≤ Nat.card E) ∧
    ∃ x y : CFSG.Sporadic.Fi23.J, x ∈ CFSG.Sporadic.Fi23.lvl 2 ∧ y ∈ CFSG.Sporadic.Fi23.lvl 2 ∧
      x * y * x⁻¹ * y⁻¹ = CFSG.Sporadic.Fi23.d := U62Final.u62_facts

end Certificates
