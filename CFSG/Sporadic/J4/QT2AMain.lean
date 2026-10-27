module

public import CFSG.Sporadic.J4.QT2ACons
public import CFSG.Sporadic.J4.QT2LocCntMain

public section

namespace CFSG.Sporadic.J4.QT2A

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem constrained_centralizer_eta_1131 :
    ∃ N : Subgroup J, N ≤ Subgroup.centralizer ({eta uJ 11 1131} : Set J) ∧
      (∀ q ∈ Subgroup.centralizer ({eta uJ 11 1131} : Set J), ∀ e ∈ N, q * e * q⁻¹ ∈ N) ∧
      IsPGroup 2 ↥N ∧
      ∀ q ∈ Subgroup.centralizer ({eta uJ 11 1131} : Set J),
        (∀ e ∈ N, q * e = e * q) → q ∈ N :=
  exists_normal_two_group_selfcentralizing j4Facts.mat QT2.card_centralizer_eta_1131

theorem constrained_centralizer_eta_three :
    ∃ N : Subgroup J, N ≤ Subgroup.centralizer ({eta uJ 11 3} : Set J) ∧
      (∀ q ∈ Subgroup.centralizer ({eta uJ 11 3} : Set J), ∀ e ∈ N, q * e * q⁻¹ ∈ N) ∧
      IsPGroup 2 ↥N ∧
      ∀ q ∈ Subgroup.centralizer ({eta uJ 11 3} : Set J),
        (∀ e ∈ N, q * e = e * q) → q ∈ N := by
  obtain ⟨g, -, hg⟩ := QT2.exists_conj_eta_three_of_mem_zMasks QT2.mem_zMasks_1131
  have h := constrained_centralizer_eta_1131
  rw [← hg] at h
  exact constrained_of_conj g _ h

end CFSG.Sporadic.J4.QT2A
