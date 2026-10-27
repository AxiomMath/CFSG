module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115CoverAltInputs
import Certificates.Kernel.LocalQT.Small.Perm7

public section

namespace Certificates

open CFSG.KC.LQT.S CFSG.KD.LQT.Perm7 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.QuasithinUnique.Ch1.Seven in
open Equiv Equiv.Perm in
theorem certificate4156 : (∀ t : Perm (Fin 7), Perm.sign t = 1 → t * t = 1 → t ≠ 1 →
          ∃ g : Perm (Fin 7), Perm.sign g = 1 ∧ g * a7 * g⁻¹ = t)
    ∧ (∀ g : Perm (Fin 7), g ^ 9 = 1 → g ^ 3 = 1)
    ∧ (∀ σ : Perm (Fin 7), σ.cycleType = {2, 2, 2} → σ * σ = 1 ∧
          ∃ x : Perm (Fin 7), Perm.sign x = 1 ∧
            (x⁻¹ * σ⁻¹ * x * σ) * (x⁻¹ * σ⁻¹ * x * σ) = 1 ∧ x⁻¹ * σ⁻¹ * x * σ ≠ 1) := (s4156 _ ca7 k4156)

end Certificates
