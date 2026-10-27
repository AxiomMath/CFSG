module

public import CFSG.Sporadic.SmallOddCore.J2Data
import Certificates.Kernel.J2Five.Final

public section

namespace Certificates

open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore in
theorem certificate55106 : (∀ x ∈ j2P, orderOf x = 3 → ∃ u₁ ∈ j2P, ∃ u₂ ∈ j2P, u₁ * u₁ = 1 ∧ u₂ * u₂ = 1 ∧
      u₁ * u₂ = u₂ * u₁ ∧ x * u₁ * x⁻¹ = u₂ ∧ x * u₂ * x⁻¹ = u₁ * u₂ ∧ u₂ ≠ u₁) ∧
    (∀ x ∈ j2P, orderOf x = 5 →
      ¬ 8 ∣ Nat.card ↥(j2R ⊓ Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 315))))) := CFSG.KD.J2Five.facts

end Certificates
