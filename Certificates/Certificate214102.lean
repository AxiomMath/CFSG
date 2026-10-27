module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeChar
import Certificates.Kernel.E6TwA2.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LieType.Steinberg.Adjoint in
theorem certificate214102 : ∀ x y z : Fin Tag.E6.rank → ZMod 3,
    (∀ α, IsRoot Tag.E6 α → triPairing x α = 0 → triPairing y α = 0 → triPairing z α ≠ 0) →
    ∃ β₁ β₂ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 β₁ ∧ IsRoot Tag.E6 β₂ ∧
      IsRoot Tag.E6 (β₁ + β₂) ∧ triPairing x (β₁ - β₂) = 0 ∧ triPairing y (β₁ - β₂) = 0 ∧
      triPairing z (β₁ - β₂) = 0 ∧
      ∃ δ : Fin Tag.E6.rank → ℤ, triPairing x δ = 0 ∧ triPairing y δ = 0 ∧
        triPairing z δ = 0 ∧ ¬ (3 : ℤ) ∣ iform δ (β₁ + β₂) :=
  KernelE6TwA2.e6TwA2_plane

end Certificates
