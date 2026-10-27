module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
import Certificates.Kernel.LocalComp.L34FWGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.PSL3Four in
theorem certificate22256 : (∀ P : Equiv.Perm (Fin 42) → Prop,
      (∀ x y, x ∈ S → y ∈ S → x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 → x * y = y * x →
        P x → P y) →
      ∀ x₀ ∈ S, x₀ * x₀ = 1 → x₀ ≠ 1 → P x₀ → ∀ y ∈ S, y * y = 1 → y ≠ 1 → P y) ∧
    ∀ H : Subgroup (Equiv.Perm (Fin 42)), (∀ y ∈ S, y * y = 1 → y ≠ 1 → y ∈ H) → S ≤ H :=
  ⟨fun P hP _ hx₀S hx₀2 hx₀1 h₀ _ hyS hy2 hy1 =>
    KernelLC.L34FW.involution_closure P hP hx₀S hx₀2 hx₀1 h₀ hyS hy2 hy1,
    fun _ hH => KernelLC.L34FW.le_of_involutions hH⟩

end Certificates
