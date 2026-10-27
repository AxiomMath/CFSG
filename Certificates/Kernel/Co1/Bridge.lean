module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import Certificates.Kernel.Co1.Tables1
import Certificates.Kernel.Co1.Tables2
import Certificates.Kernel.Co1.Dce
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CertificateChecks.KernelCo1

open CFSG.KC CFSG.KC.LceS CFSG.Certificates CFSG.Certificates.LCE CertificateChecks.KernelCo2

theorem co1 : Finite TauCeti.SporadicName.Co1.Group ∧
    Nat.card TauCeti.SporadicName.Co1.Group ≤ 4157776806543360000 := by
  have u1 := s1
  have u2 := s2
  unfold Tab at u1 u2
  rw [img_eq _ (nat_lit 7) (nat_lit 14) (fun x => by change x < 7 ↔ 2 * x < 14; omega)] at u1
  rw [closure_g0] at u1
  rw [h2_eq] at u2
  have hf := h2_card.1
  have c := card_le_step' u1 (card_le_step' u2 ⟨Nat.card_pos.ne', h2_card.2⟩)
  rw [Subgroup.card_top] at c
  exact ⟨Nat.finite_of_card_ne_zero c.1, c.2.trans (Nat.le_of_ble_eq_true (by quickRfl))⟩

end CertificateChecks.KernelCo1

end
