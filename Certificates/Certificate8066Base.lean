
module

public import CFSG.Quasithin.Background.Sp4InfA6BasicInputs
import CFSG.Certificates.Kernel.PermCent.GHFast
import all CFSG.Quasithin.Background.Sp4InfA6BasicInputs
import all CFSG.Quasithin.Background.Sp4InfA6BasicBase

@[expose] public section

open CFSG CFSG.Quasithin CFSG.Quasithin.Sp4Inf Equiv
open scoped Pointwise

namespace CertificateChecks.Batch8066

private theorem card_q1_0 : Nat.card q1 = 24 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [mem_q1]
  decide +kernel

private theorem card_q2_1 : Nat.card q2 = 24 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [mem_q2]
  decide +kernel

private theorem card_s0_2 : Nat.card s0 = 8 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [mem_s0]
  decide +kernel

private theorem card_alt_six_3 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [Perm.mem_alternatingGroup]
  decide +kernel

open scoped CFSG.Certificates.Kernel.PkCV.FastDecide in
private theorem fix_aux : ∀ g : Perm (Fin 6),
    (∀ x ∈ (CFSG.Certificates.Kernel.PkCV.allPL 6).filter bs0, bs0 (g * x * g⁻¹) = true) →
      (∀ x ∈ (CFSG.Certificates.Kernel.PkCV.allPL 6).filter bq1, bq1 (g * x * g⁻¹) = true) ∧
        ∀ x ∈ (CFSG.Certificates.Kernel.PkCV.allPL 6).filter bq2, bq2 (g * x * g⁻¹) = true := by
  decide +kernel

private theorem fix_of_normalizes_s0_4 :
    ∀ g : Perm (Fin 6), (∀ x, bs0 x = true → bs0 (g * x * g⁻¹) = true) →
      (∀ x, bq1 x = true → bq1 (g * x * g⁻¹) = true) ∧
        ∀ x, bq2 x = true → bq2 (g * x * g⁻¹) = true := by
  intro g h
  obtain ⟨h1, h2⟩ := fix_aux g (CFSG.Certificates.Kernel.PkCV.mem_filter_allPL_of_forall h)
  exact ⟨CFSG.Certificates.Kernel.PkCV.forall_of_mem_filter_allPL h1,
    CFSG.Certificates.Kernel.PkCV.forall_of_mem_filter_allPL h2⟩

end CertificateChecks.Batch8066

