module

public import Certificates.Data.Holder1711.Om2Facts
import Certificates.Kernel.Om2K.BGlue
import Certificates.Kernel.Om2K.BJoin
import Certificates.Kernel.Om2K.BDefs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.BfsPinSound
import CFSG.Certificates.Kernel.Spor.RawOrbGrp
import Certificates.Kernel.Om2K.Words

public section

namespace Certificates

open CertificateChecks

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data in
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check in
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Facts in
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711 (OmGen.BadElt) in
theorem certificate197003 :
    (∀ x ∈ G wS0, ∀ y ∈ G wS0, x * x = t → y * y = t → y * x * y⁻¹ = x⁻¹ →
      (x ∈ R ∧ y ∈ R) ∨ ∃ s ∈ G wT, TwinFail x y s) ∧
    (∀ x ∈ G wSc, ∀ y ∈ G wSc, x * x = tc → y * y = tc → y * x * y⁻¹ = x⁻¹ →
      ∃ s ∈ G wCc, TwinFail x y s) ∧
    24 ≤ {p : Equiv.Perm (Fin 480) × Equiv.Perm (Fin 480) |
      ∃ s ∈ G wT, p = (s * E wI0 * s⁻¹, s * E wJ0 * s⁻¹)}.ncard ∧
    Nat.card ↥(G wCR ⊓ Subgroup.centralizer S8) ≤ 8 ∧
    ({x | x ∈ G wS0 ∧ ¬ OmGen.BadElt (G wT) R (D Zt1) x}.ncard ≤ 8 ∧
      {x | x ∈ G wP3 ∧ ¬ OmGen.BadElt (G wT) R (D Zt1) x}.ncard ≤ 1 ∧
      {x | x ∈ G wS0 ∧ ¬ OmGen.BadElt (G wT) R (D Zt4) x}.ncard ≤ 1184 ∧
      {x | x ∈ G wP3 ∧ ¬ OmGen.BadElt (G wT) R (D Zt4) x}.ncard ≤ 19) ∧
    (∀ u ∈ G wCR, u * u = 1 → (∃ g ∈ Yg, u = g * t * g⁻¹) → u ∈ Zt4) ∧
      ∀ w ∈ wFuse0, ∀ a ∈ [wI0, wJ0], ∀ b ∈ [wI0, wJ0], Commute (E w * E a * (E w)⁻¹) (E b) := KernelOm2.certB

end Certificates
