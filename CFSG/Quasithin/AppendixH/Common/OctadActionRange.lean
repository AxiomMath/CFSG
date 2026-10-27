module

public import CFSG.Quasithin.AppendixH.Common.OctadAction
public import CFSG.Quasithin.AppendixH.Common.OctadPtStabCard

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Monster.Code

theorem range_octAct {O : Finset (Fin 24)} (hO : IsOctad O) :
    (octAct O).range = alternatingGroup ↥O := by
  have hcardKer : Nat.card (octAct O).ker = 16 := by
    rw [ker_octAct O]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (octFix_le_octStab O)).toEquiv).trans
      (card_octFix hO)
  have hcardRange : Nat.card (octAct O).range = 20160 := by
    have h := Subgroup.card_ker_mul_card_range (octAct O)
    rw [hcardKer, card_octStab hO] at h
    omega
  have hcardPerm : Nat.card (Equiv.Perm ↥O) = 40320 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_coe, hO.1]
    norm_num
  have hindex : (octAct O).range.index = 2 := by
    have h := Subgroup.card_mul_index (octAct O).range
    rw [hcardRange, hcardPerm] at h
    omega
  exact Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex

end CFSG.ASVolI.AppH
