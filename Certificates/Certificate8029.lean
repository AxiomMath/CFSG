module

public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.LocalQT.SR.RuLocal
public import CFSG.Open.LocalVocabulary

public section

namespace Certificates

open CertificateChecks

open scoped commutatorElement in
theorem certificate8029 :
    (∃ x y h : CFSG.Blueprint.NativeSporadic.Ru, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧
      Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set CFSG.Blueprint.NativeSporadic.Ru)) = 3 ^ 3 ∧
      h * x * h⁻¹ = x ^ 2 * y ^ 1 * ⁅x, y⁆ ^ 1 ∧ h * y * h⁻¹ = x ^ 2 * y ^ 2 * ⁅x, y⁆ ^ 1 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 2) ∧ (∃ x y h : CFSG.Blueprint.NativeSporadic.Ru, x ^ 5 = 1 ∧
      y ^ 5 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set CFSG.Blueprint.NativeSporadic.Ru)) = 5 ^ 3 ∧
      h * x * h⁻¹ = x ^ 3 * y ^ 0 * ⁅x, y⁆ ^ 3 ∧ h * y * h⁻¹ = x ^ 0 * y ^ 3 * ⁅x, y⁆ ^ 4 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 4) := ⟨KernelLocalQT.ru_sylow3, KernelLocalQT.ru_sylow5⟩

end Certificates
