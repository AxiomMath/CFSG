module

public import Certificates.Data.Holder1711.Om1Facts
import Certificates.Kernel.Om1K.Cert
import Certificates.Kernel.Om1K.OrbDefs
import Certificates.Kernel.Om1K.Enum
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Om1K.BDefs
import CFSG.Certificates.Kernel.BfsPinSound
import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

namespace Certificates

open CertificateChecks

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data in
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check in
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Facts in
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711 (OmGen.BadElt) in
theorem certificate197001 :
    (E CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data.wT0 = t ∧ E CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data.wI0 * E CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data.wI0 = t ∧ E CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data.wJ0 * E CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data.wJ0 = t ∧ E CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data.wJ0 * E CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data.wI0 * (E CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data.wJ0)⁻¹ = (E CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data.wI0)⁻¹ ∧
      E wG1 * t * (E wG1)⁻¹ = t * z ∧ (∀ w ∈ wT ++ [wS1], Commute (E w) t) ∧
      (∀ w ∈ wCa, Commute (E w) ta) ∧ (∀ w ∈ wCc, Commute (E w) tc) ∧ tb = z * ta) ∧
    (Nat.card (G wS0) = 4096 ∧ Nat.card (G CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data.wP3) = 27 ∧ Nat.card (G wSa) = 2048 ∧
      Nat.card (G wPa3) = 9 ∧ Nat.card (G wPa5) = 5 ∧ Nat.card (G wSc) = 1024 ∧
      Nat.card (G CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data.wPc) = 3) ∧
    (3150 ≤ (orb (G wX) (neg 15)).ncard ∧ 3780 ≤ (orb (G wX) (neg 3)).ncard ∧
      113400 ≤ (orb (G wX) (neg 23)).ncard) ∧
    (∀ g ∈ G wX, g '' neg 15 = neg 15 ∨ g '' neg 15 = E wG1 '' neg 15 ∨
      ∃ w ∈ wSub, ∃ s ∈ G wT, g '' neg 15 = (s * E w) '' neg 15) ∧
    (∀ w ∈ wSub, 3150 ≤ (orb (G (wT ++ [w])) (neg 15)).ncard) ∧
    (∀ d ∈ maskData, d.2.1 < 4 ∧ E d.2.2 * e d.1 * (E d.2.2)⁻¹ = e (repMasks.getD d.2.1 0)) ∧
    (∀ x ∈ G wS0, ∀ y ∈ G wS0, x * x = t → y * y = t → y * x * y⁻¹ = x⁻¹ →
      (x ∈ R ∧ y ∈ R) ∨ (x ∈ R' ∧ y ∈ R') ∨ ∃ s ∈ G wT, TwinFail x y s) ∧
    ((∀ x ∈ G wSa, x * x ≠ tb) ∧ ∀ x ∈ G wSa, ∀ y ∈ G wSa, x * x = ta → y * y = ta →
      y * x * y⁻¹ ≠ x⁻¹) ∧
    (∀ x ∈ G wSc, ∀ y ∈ G wSc, x * x = tc → y * y = tc → y * x * y⁻¹ = x⁻¹ →
      ∃ s ∈ G wCc, TwinFail x y s) ∧
    576 ≤ {p | ∃ s ∈ G wT, p = tup s}.ncard ∧
    ({x | x ∈ G wS0 ∧ ¬ OmGen.BadElt (G wT) (↑R ∪ ↑R') D x}.ncard ≤ 64 ∧
      {x | x ∈ G CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data.wP3 ∧ ¬ OmGen.BadElt (G wT) (↑R ∪ ↑R') D x}.ncard ≤ 3) ∧
    Nat.card R ≤ 8 := KernelOm1.cert

end Certificates
