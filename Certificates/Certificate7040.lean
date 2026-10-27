module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoRefInputs
import Certificates.Kernel.LocalComp.WittA7040

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelLC.Witt in
open CFSG CFSG.Quasithin CFSG.Quasithin.L34Amalgam MulAction CFSG.ComponentClassification.WittDesign in
open CFSG.Quasithin.Asc94 CFSG.Sporadic.Mathieu in
theorem certificate7040 :
    ((refa : Equiv.Perm (Fin 22)) 0 = 0 ∧ (refa : Equiv.Perm (Fin 22)) 1 = 1 ∧
       (refb : Equiv.Perm (Fin 22)) 0 = 0 ∧ (refb : Equiv.Perm (Fin 22)) 1 = 1 ∧
       refa * refa = 1 ∧ refb ^ 3 = 1 ∧ (refa * refb) ^ 5 = 1)
    ∧ (∀ x : Fin 16, ((crd x : M22) : Equiv.Perm (Fin 22)) 0 = 0 ∧
       ((crd x : M22) : Equiv.Perm (Fin 22)) 1 = 1)
    ∧ (∀ x y : Fin 16, crd (bxor x y) = crd x * crd y)
    ∧ (∀ x : Fin 16, crd x = 1 → x = 0)
    ∧ (crd 0 = 1)
    ∧ (∀ x : Fin 16, refa * crd x * refa⁻¹ = crd (lin refA x))
    ∧ (∀ x : Fin 16, refb * crd x * refb⁻¹ = crd (lin refB x))
    ∧ (∀ s ∈ cWords, ∀ t ∈ cWords, cOfWord s = cOfWord t → s = t)
    ∧ (∀ s ∈ cWords, (∃ t ∈ cWords, cOfWord s * refa = cOfWord t) ∧
       (∃ t ∈ cWords, cOfWord s * refb = cOfWord t) ∧
         ∃ t ∈ cWords, cOfWord s * refb⁻¹ = cOfWord t)
    ∧ (∀ s ∈ cWords, ∀ x : Fin 16, cOfWord s = crd x → x = 0)
    ∧ (cOfWord "" = 1)
    ∧ (∀ j : Fin 5, j ≠ 4 → ∀ x : Fin 16, ∃ y : Fin 16,
       gen j * crd x * (gen j)⁻¹ = crd y)
    ∧ (cWords.Nodup ∧ cWords.length = 60) :=
  ⟨ref_facts, crd_facts, crd_mul, crd_eq_one, crd_zero, crd_conj_a, crd_conj_b, cWords_inj,
    cWords_closed, cWords_crd, cWords_one, crd_conj_gen, card_barC⟩

end Certificates
