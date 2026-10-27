module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeClasses
import Certificates.Kernel.O8Sq.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight CFSG.Sporadic.Schreier in
theorem certificate272020 :
    (∀ c ∈ omegaT, orderOf c = 4 → ∃ g ∈ omegaT, g * (c * c) = (c * c) * g ∧
        (c * (g * c * g⁻¹)) * (c * (g * c * g⁻¹)) = 1 ∧ c * (g * c * g⁻¹) ≠ 1 ∧
        c * (g * c * g⁻¹) ≠ c * c) ∧
    Nat.card (centralizerIn omegaT (mainPerm 0)) = 110592 ∧
    Nat.card (centralizerIn omegaT (mainPerm 1)) = 46080 ∧
    Nat.card (centralizerIn omegaT (mainPerm 2)) = 3072 :=
  ⟨fun c hc ho => KernelO8Sq.o8sq_wit c hc ho, KernelO8Sq.o8sq_card0, KernelO8Sq.o8sq_card1,
    KernelO8Sq.o8sq_card2⟩

end Certificates
