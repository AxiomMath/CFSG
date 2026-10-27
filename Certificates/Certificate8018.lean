module

public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.LocalQT.SR.HSLocal
public import CFSG.Open.LocalVocabulary

public section

namespace Certificates

open CertificateChecks

open scoped commutatorElement in
theorem certificate8018 :
    (∃ x y h : CFSG.Blueprint.NativeSporadic.HS, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y = y * x ∧
      Nat.card (Subgroup.closure ({x, y} : Set CFSG.Blueprint.NativeSporadic.HS)) = 3 ^ 2 ∧
      h * x * h⁻¹ = x ^ 1 * y ^ 0 ∧ h * y * h⁻¹ = x ^ 2 * y ^ 2) ∧
      (∃ x y h : CFSG.Blueprint.NativeSporadic.HS, x ^ 5 = 1 ∧ y ^ 5 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧
      Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set CFSG.Blueprint.NativeSporadic.HS)) = 5 ^ 3 ∧
      h * x * h⁻¹ = x ^ 3 * y ^ 0 * ⁅x, y⁆ ^ 0 ∧ h * y * h⁻¹ = x ^ 0 * y ^ 3 * ⁅x, y⁆ ^ 0 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 4) := ⟨KernelLocalQT.hs_sylow3, KernelLocalQT.hs_sylow5⟩

end Certificates
