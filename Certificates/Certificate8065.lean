module

public import CFSG.Quasithin.Background.Sp4InfA6BasicInputs
import CFSG.Quasithin.Background.Sp4InfA6BasicBase

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.Sp4Inf Equiv
open scoped Pointwise

namespace CertificateChecks.Batch8065

open CFSG CFSG.Quasithin CFSG.Quasithin.Sp4Inf Equiv
open scoped Pointwise

private theorem exists_not_mem_q1_0 :
    ∃ y : Perm (Fin 6), y ∈ alternatingGroup (Fin 6) ∧ y ∉ q1 := by
  refine ⟨Equiv.swap 0 4 * Equiv.swap 1 5, ?_, ?_⟩
  · rw [Perm.mem_alternatingGroup]
    decide +kernel
  · rw [mem_q1]
    decide +kernel

private theorem exists_not_mem_q2_1 :
    ∃ y : Perm (Fin 6), y ∈ alternatingGroup (Fin 6) ∧ y ∉ q2 := by
  refine ⟨Equiv.swap 0 4 * Equiv.swap 1 5, ?_, ?_⟩
  · rw [Perm.mem_alternatingGroup]
    decide +kernel
  · rw [mem_q2]
    decide +kernel

private theorem card_sylow_alt6_2 : 2 ^ padicValNat 2 360 = 8 := by
  decide +kernel

end CertificateChecks.Batch8065

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.Sp4Inf Equiv in
open scoped Pointwise in
theorem certificate8065 : (∃ y : Perm (Fin 6), y ∈ alternatingGroup (Fin 6) ∧ y ∉ q1)
    ∧ (∃ y : Perm (Fin 6), y ∈ alternatingGroup (Fin 6) ∧ y ∉ q2)
    ∧ (2 ^ padicValNat 2 360 = 8) := by
  exact ⟨CertificateChecks.Batch8065.exists_not_mem_q1_0, CertificateChecks.Batch8065.exists_not_mem_q2_1, CertificateChecks.Batch8065.card_sylow_alt6_2⟩

end Certificates
