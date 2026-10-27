module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4UBasic

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8)

theorem isElemAb_of {H : Subgroup P8} {k : ℕ} (h1 : CFSG.IsElementaryAbelian 2 H)
    (h2 : Nat.card H = 2 ^ k) : IsElemAb 2 k H := by
  unfold IsElemAb
  exact ⟨h1, h2⟩

theorem A_U_data_basic :
    (Ua ≠ Ub ∧ Ua ⊓ Ub = ⊥ ∧ IsElemAb 2 4 Ua ∧ IsElemAb 2 2 (Ua ⊓ Cen cc) ∧
      IsElemAb 2 2 (Ua ⊓ Cen dd) ∧ Ua ⊓ Cen (cc * dd) = ⊥ ∧ Ua ⊓ Cen (cc * dd ^ 2) = ⊥) ∧
    (IsElemAb 2 4 Ub ∧ IsElemAb 2 2 (Ub ⊓ Cen cc) ∧ IsElemAb 2 2 (Ub ⊓ Cen dd) ∧
      Ub ⊓ Cen (cc * dd) = ⊥ ∧ Ub ⊓ Cen (cc * dd ^ 2) = ⊥) := by
  refine ⟨⟨Ua_ne_Ub, Ua_inf_Ub,
    isElemAb_of Ua_isEA (by rw [Ua_card]; norm_num),
    isElemAb_of (isEA2_of_le_Ua inf_le_left) (by rw [Ua_cent_cc_card]; norm_num),
    isElemAb_of (isEA2_of_le_Ua inf_le_left) (by rw [Ua_cent_dd_card]; norm_num),
    Ua_cent_cd, Ua_cent_cd2⟩, ?_⟩
  exact ⟨isElemAb_of Ub_isEA (by rw [Ub_card]; norm_num),
    isElemAb_of (isEA2_of_le_Ub inf_le_left) (by rw [Ub_cent_cc_card]; norm_num),
    isElemAb_of (isEA2_of_le_Ub inf_le_left) (by rw [Ub_cent_dd_card]; norm_num),
    Ub_cent_cd, Ub_cent_cd2⟩

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
