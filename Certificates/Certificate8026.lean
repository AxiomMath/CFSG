
module


public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalInputs
import Certificates.Kernel.LocalQT.Word.Mathieu

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.SectionRank CFSG.Blueprint in
open scoped commutatorElement in
theorem certificate8026 : (let x := mathieuWord m12LocA m12LocB m12WordX.toList
      let y := mathieuWord m12LocA m12LocB m12WordY.toList
      let h := mathieuWord m12LocA m12LocB m12WordH.toList
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
        (Function.Injective fun t : Fin 3 × Fin 3 × Fin 3 =>
          x ^ (t.1 : ℕ) * y ^ (t.2.1 : ℕ) * ⁅x, y⁆ ^ (t.2.2 : ℕ)) ∧
        h * x * h⁻¹ = x ^ 2 * y ^ 0 * ⁅x, y⁆ ^ 1 ∧
        h * y * h⁻¹ = x ^ 0 * y ^ 2 * ⁅x, y⁆ ^ 1 ∧
        h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 1)
    ∧ (let x := mathieuWord m24LocA m24LocB m24WordX.toList
      let y := mathieuWord m24LocA m24LocB m24WordY.toList
      let h := mathieuWord m24LocA m24LocB m24WordH.toList
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
        (Function.Injective fun t : Fin 3 × Fin 3 × Fin 3 =>
          x ^ (t.1 : ℕ) * y ^ (t.2.1 : ℕ) * ⁅x, y⁆ ^ (t.2.2 : ℕ)) ∧
        h * x * h⁻¹ = x ^ 0 * y ^ 1 * ⁅x, y⁆ ^ 0 ∧
        h * y * h⁻¹ = x ^ 2 * y ^ 0 * ⁅x, y⁆ ^ 0 ∧
        h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 1) := KernelLocalQT.mathieu_local

end Certificates
