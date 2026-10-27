module

public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.LocalQT.SR.J2Local
public import CFSG.Open.LocalVocabulary

public section

namespace Certificates

open CertificateChecks

open scoped commutatorElement in
theorem certificate8020 :
    (∃ x y h : CFSG.Blueprint.NativeSporadic.J2, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧
      Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set CFSG.Blueprint.NativeSporadic.J2)) = 3 ^ 3 ∧
      h * x * h⁻¹ = x ^ 2 * y ^ 1 * ⁅x, y⁆ ^ 2 ∧ h * y * h⁻¹ = x ^ 1 * y ^ 0 * ⁅x, y⁆ ^ 0 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 2) ∧ (∃ x y h : CFSG.Blueprint.NativeSporadic.J2, x ^ 5 = 1 ∧
      y ^ 5 = 1 ∧ x * y = y * x ∧
      Nat.card (Subgroup.closure ({x, y} : Set CFSG.Blueprint.NativeSporadic.J2)) = 5 ^ 2 ∧
      h * x * h⁻¹ = x ^ 0 * y ^ 4 ∧ h * y * h⁻¹ = x ^ 4 * y ^ 0) := ⟨KernelLocalQT.j2_sylow3, KernelLocalQT.j2_sylow5⟩

end Certificates
