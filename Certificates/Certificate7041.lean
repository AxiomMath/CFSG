module

public import CFSG.Quasithin.Recognition.M22UniqueDataInputs
import Certificates.Kernel.LocalComp.WittA7041

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.Asc94 CFSG.ComponentClassification.WittDesign in
open CFSG.Sporadic.Mathieu in
theorem certificate7041 :
    ((m22Tbar : Equiv.Perm (Fin 22)) 0 = 1 ∧
       (m22Tbar : Equiv.Perm (Fin 22)) 1 = 0 ∧ PresHex m22Tbar)
    ∧ ((m22I1 : Equiv.Perm (Fin 22)) 0 = 1 ∧
       (m22I1 : Equiv.Perm (Fin 22)) 1 = 2 ∧ PresHex m22I1)
    ∧ ((m22I2 : Equiv.Perm (Fin 22)) 0 = 2 ∧
       (m22I2 : Equiv.Perm (Fin 22)) 1 = 0 ∧ PresHex m22I2)
    ∧ (((m22Fix2 : Equiv.Perm (Fin 22)) 0 = 0 ∧ (m22Fix2 : Equiv.Perm (Fin 22)) 1 = 2 ∧
         PresHex m22Fix2) ∧
       ((m22Fix9 : Equiv.Perm (Fin 22)) 0 = 0 ∧ (m22Fix9 : Equiv.Perm (Fin 22)) 1 = 9 ∧
         PresHex m22Fix9) ∧
       ((m22Fix17 : Equiv.Perm (Fin 22)) 0 = 0 ∧ (m22Fix17 : Equiv.Perm (Fin 22)) 1 = 17 ∧
         PresHex m22Fix17) ∧
       ((m22Fix19 : Equiv.Perm (Fin 22)) 0 = 0 ∧ (m22Fix19 : Equiv.Perm (Fin 22)) 1 = 19 ∧
         PresHex m22Fix19))
    ∧ ((m22G : Equiv.Perm (Fin 22)) 0 = 0 ∧ (m22G : Equiv.Perm (Fin 22)) 1 = 1 ∧
       (∀ p : Fin 22, (m22G : Equiv.Perm (Fin 22)) p ∈ m22HexadF ↔ p ∈ m22H1F) ∧
       ¬ PresHex m22G)
    ∧ ((∀ p, (m22E1 : Equiv.Perm (Fin 22)) p = m22F1 p) ∧
       ∀ p, (m22E2 : Equiv.Perm (Fin 22)) p = m22F2 p)
    ∧ ((m22F1 0 = 0 ∧ m22F1 1 = 1 ∧ (∀ p, m22F1 p ∈ m22HexadF ↔ p ∈ m22HexadF) ∧
         ∀ p, m22F1 p ∈ m22H1F ↔ p ∈ m22H1F) ∧
       (m22F2 0 = 0 ∧ m22F2 1 = 1 ∧ (∀ p, m22F2 p ∈ m22HexadF ↔ p ∈ m22HexadF) ∧
         ∀ p, m22F2 p ∈ m22H1F ↔ p ∈ m22H1F))
    ∧ (m22Count (fun σ => σ 0 = 0 ∧ σ 1 = 1) = 960)
    ∧ (m22Count (fun σ => σ 0 = 0 ∧ σ 1 = 1 ∧
       ∀ p ∈ m22HexadL, σ p ∈ m22HexadL) = 192)
    ∧ (m22Count (fun σ => σ 0 = 0 ∧ σ 1 = 1 ∧
       (∀ p : Fin 22, σ (m22F1 p) = m22F1 (σ p)) ∧ ∀ p : Fin 22, σ (m22F2 p) = m22F2 (σ p)) = 1) := KernelLC.Witt.facts7041

end Certificates
