module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeCharData
import CFSG.Certificates.Kernel.E6PlaneLinesSound
import Certificates.Kernel.E6PlaneLines.Checks

public section

namespace Certificates

open CertificateChecks.KernelE6PlaneLines

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar in
theorem certificate716800 : ∀ b₀ b₁ : Fin Tag.E6.rank → ZMod 3,
    (∀ c₀ c₁ : ZMod 3, c₀ • b₀ + c₁ • b₁ = 0 → c₀ = 0 ∧ c₁ = 0) →
    6 < {γ | IsRoot .E6 γ ∧ triPairing b₀ γ = 0 ∧ triPairing b₁ γ = 0}.ncard →
    ∀ w : WeylGroup .E6, w ∈ charStabilizer (triChar b₀) → w ∈ charStabilizer (triChar b₁) →
      triPairing b₀ (fun i => ((w • e6Omega3) i - e6Omega3 i) / 3) = 0 ∧
        triPairing b₁ (fun i => ((w • e6Omega3) i - e6Omega3 i) / 3) = 0 :=
  fun b₀ b₁ hind hlarge _ h₀ h₁ =>
    CFSG.KC.E6PlaneLines.shift_eq_zero_of_checks lines_check_A lines_check_B ns_mask_check
      pass_one_check b₀ b₁ hind hlarge h₀ h₁

end Certificates
