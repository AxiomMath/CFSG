
module

public import CFSG.Quasithin.Background.Sp4InfA6BasicInputs
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

private theorem fix_of_normalizes_s0_4 :
    ∀ g : Perm (Fin 6), (∀ x, bs0 x = true → bs0 (g * x * g⁻¹) = true) →
      (∀ x, bq1 x = true → bq1 (g * x * g⁻¹) = true) ∧
        ∀ x, bq2 x = true → bq2 (g * x * g⁻¹) = true := by
  decide +kernel

end CertificateChecks.Batch8066

