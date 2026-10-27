module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeClasses
import Certificates.Kernel.OmegaEight.Roots127Sound
import Certificates.Kernel.OmegaEight.Roots127Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight in
theorem certificate127 :
    (gen 8 * (gen 8 * gen 8) = 1 ∧ gen 9 * gen 9 = 1 ∧ gen 9 * gen 8 * gen 9 = gen 8 * gen 8) ∧
    (gen 8 ∉ omegaT ∧ gen 8 * gen 8 ∉ omegaT) ∧
    ∀ {i : ℕ}, i < 3 → ∀ {j : Equiv.Perm (Fin 360)}, j ∈ autT → j ∉ omegaT →
      j * j = mainPerm i →
      (∃ c ∈ omegaT, c * mainPerm i = mainPerm i * c ∧ ∃ k : ℕ,
          (j⁻¹ * c * j * c⁻¹) ^ k ≠ 1 ∧ ((j⁻¹ * c * j * c⁻¹) ^ k) ^ 3 = 1) ∨
        ∀ u ∈ omegaT, u * u = mainPerm i → j * u * j⁻¹ ≠ u⁻¹ :=
  ⟨KernelO8.rels127, KernelO8.rho_not_mem127, KernelO8.outer_root127⟩

end Certificates
