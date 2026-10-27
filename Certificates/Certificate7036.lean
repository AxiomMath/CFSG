
module

public import CFSG.Quasithin.Recognition.L34AmalgamDataInputs
import Certificates.Kernel.L34Pk.A7036

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.L34Amalgam MulAction CFSG.ComponentClassification.WittDesign in
open CFSG.Quasithin.Asc94 CFSG.Sporadic.Mathieu in
theorem certificate7036 :
    (∀ j : Fin 5, j.val < 3 → (gen j : Equiv.Perm (Fin 22)) 0 = 0 ∧
       (gen j : Equiv.Perm (Fin 22)) 1 = 1 ∧
       ∀ p ∈ m22HexadL, (gen j : Equiv.Perm (Fin 22)) p ∈ m22HexadL)
    ∧ ((bT1 : Equiv.Perm (Fin 22)) 0 = 0 ∧ (bT1 : Equiv.Perm (Fin 22)) 1 = 1 ∧
       ¬ (∀ p ∈ m22HexadL, (bT1 : Equiv.Perm (Fin 22)) p ∈ m22HexadL) ∧ bT1 * bT1 = 1 ∧
       (bT2 : Equiv.Perm (Fin 22)) 0 = 0 ∧ (bT2 : Equiv.Perm (Fin 22)) 1 ≠ 1 ∧
       (∀ p ∈ m22HexadL, (bT2 : Equiv.Perm (Fin 22)) p ∈ m22HexadL) ∧ bT2 * bT2 = 1)
    ∧ (∀ w ∈ amalRels, evalW gen w = 1)
    ∧ (∀ i : Fin 12, IsGood i → evalW gen (extra i 3) = 1) := KernelL34.facts7036

end Certificates
