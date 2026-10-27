
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7Inputs
import Certificates.Kernel.LocalQT.Small.Perm7

public section

namespace Certificates

open CFSG.KC.LQT.S CFSG.KD.LQT.Perm7 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.L246 CFSG.QuasithinUnique.L246.C123 in
open Equiv in
theorem certificate4128 : (∀ a ∈ sylowSet, ∀ b ∈ sylowSet, a * b ∈ sylowSet)
    ∧ (∀ a ∈ sylowSet, a⁻¹ ∈ sylowSet)
    ∧ ((1 : Perm (Fin 7)) ∈ sylowSet)
    ∧ (sylowSet.card = 8)
    ∧ (∀ a ∈ sylowSet, Perm.sign a = 1)
    ∧ (∀ a ∈ kleinSet, ∀ b ∈ kleinSet, a * b ∈ kleinSet)
    ∧ (∀ a ∈ kleinSet, a⁻¹ ∈ kleinSet)
    ∧ ((1 : Perm (Fin 7)) ∈ kleinSet)
    ∧ (kleinSet.card = 4)
    ∧ (kleinSet ⊆ sylowSet)
    ∧ (x7 ∈ kleinSet)
    ∧ (y7 ∈ kleinSet)
    ∧ (z7 ∈ sylowSet)
    ∧ (∀ g : Perm (Fin 7), Perm.sign g = 1 →
          g * x7 * g⁻¹ ∈ sylowSet → g * y7 * g⁻¹ ∈ sylowSet → g * z7 * g⁻¹ ∈ sylowSet →
            g ∈ sylowSet)
    ∧ (∀ c : Perm (Fin 7), Perm.sign c = 1 →
          c * x7 * c⁻¹ ∈ sylowSet → c * y7 * c⁻¹ ∈ sylowSet →
            (c * x7 * c⁻¹ ∈ kleinSet ∧ c * y7 * c⁻¹ ∈ kleinSet))
    ∧ ((Finset.univ.filter fun g : Perm (Fin 7) =>
            Perm.sign g = 1 ∧ g * x7 * g⁻¹ ∈ kleinSet ∧ g * y7 * g⁻¹ ∈ kleinSet).card = 72)
    ∧ (z7 * y7 ≠ y7 * z7) := (s4128 _ _ _ cx7 cy7 cz7 k4128)

end Certificates
