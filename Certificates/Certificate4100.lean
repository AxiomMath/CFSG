module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115CoverAltInputs
import Certificates.Kernel.LocalQT.Small.Perm7

public section

namespace Certificates

open CFSG.KC.LQT.S CFSG.KD.LQT.Perm7 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.QuasithinUnique.Ch1.Six in
open Equiv Equiv.Perm in
theorem certificate4100 : (∀ t : Perm (Fin 6), Perm.sign t = 1 → t * t = 1 → t ≠ 1 →
          ∃ g : Perm (Fin 6), Perm.sign g = 1 ∧ g * a6 * g⁻¹ = t)
    ∧ (∀ g : Perm (Fin 6), g ^ 9 = 1 → g ^ 3 = 1)
    ∧ (∀ a b : Fin 6, a ≠ b → ∃ x : Perm (Fin 6), Perm.sign x = 1 ∧
          (x⁻¹ * (swap a b)⁻¹ * x * swap a b) * (x⁻¹ * (swap a b)⁻¹ * x * swap a b) = 1 ∧
          x⁻¹ * (swap a b)⁻¹ * x * swap a b ≠ 1) := (s4100 _ ca6 k4100)

end Certificates
