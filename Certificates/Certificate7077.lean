module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoCertInputs
import Certificates.Kernel.L34Pk.A7077

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.L34Amalgam MulAction CFSG.ComponentClassification.WittDesign in
open CFSG.Quasithin.Asc94 CFSG.CosetTable in
theorem certificate7077 :
    (m22Count (fun σ => ∀ y ∈ m22HexadL, σ y = y) = 16)
    ∧ (m22Count (fun σ => (∀ y ∈ m22HexadL, σ y = y) ∧ ¬ ∀ x, σ (σ x) = x) = 0)
    ∧ (m22Count (fun σ => (σ 0 = 0 ∧ ∀ p ∈ m22HexadL, σ p ∈ m22HexadL) ∧ σ 3 = 3) = 60)
    ∧ (m22Count (fun σ => (∀ y ∈ m22HexadL, σ y = y) ∧ σ 3 = 3 ∧ ¬ ∀ x, σ x = x) = 0)
    ∧ (m22Count (fun σ => (∀ y ∈ m22HexadL, σ y = y) ∧
        (∀ x, σ ((b2r : Equiv.Perm (Fin 22)) x) = (b2r : Equiv.Perm (Fin 22)) (σ x)) ∧
          ¬ ∀ x, σ x = x) = 0)
    ∧ ((((a2r : Equiv.Perm (Fin 22)) 0 = 0 ∧
        ∀ p ∈ m22HexadL, (a2r : Equiv.Perm (Fin 22)) p ∈ m22HexadL) ∧
          (a2r : Equiv.Perm (Fin 22)) 3 = 3) ∧
        (((b2r : Equiv.Perm (Fin 22)) 0 = 0 ∧
          ∀ p ∈ m22HexadL, (b2r : Equiv.Perm (Fin 22)) p ∈ m22HexadL) ∧
            (b2r : Equiv.Perm (Fin 22)) 3 = 3) ∧
        a2r * a2r = 1 ∧ b2r ^ 3 = 1 ∧ (a2r * b2r) ^ 5 = 1)
    ∧ (cWords.Nodup ∧ cWords.length = 60)
    ∧ ((cWords.map fun s => tab (c2OfWord s)).Nodup) := KernelL34.facts7077

end Certificates
