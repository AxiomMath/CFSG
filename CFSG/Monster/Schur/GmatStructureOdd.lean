module

public import CFSG.Monster.Schur.GmatStructureSplit

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Schur

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Visible CFSG.Monster.VisQuot
  CFSG.Monster.VisCert Subgroup

theorem natCard_PMat :
    Nat.card PMat = 2 ^ 25 * (2 ^ 11 * 244823040) := by
  have h := natCard_imPhi_mul (S := PMat) PMat_le_Gvis
  have e : Qmat ⊓ PMat = Qmat := inf_eq_left.2 le_sup_left
  rw [imPhi_PMat_eq_Nvis, natCard_Nvis, e, natCard_Qmat] at h
  rw [← h]
  ring

theorem odd_relIndex_PMat_of
    (hG : Nat.card Gmat = 97239461142009186000 * (11707448673375 * (2 ^ 24 * 42305421312000))) :
    Odd (PMat.relIndex Gmat) := by
  have h := Subgroup.relIndex_mul_card PMat Gmat
  have e : PMat ⊓ Gmat = PMat := inf_eq_left.2 PMat_le_Gmat
  rw [e, natCard_PMat, hG] at h
  have hr : PMat.relIndex Gmat = 48027346889627052019030652834765625 := by
    refine Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2 ^ 25 * (2 ^ 11 * 244823040)) ?_
    rw [h]
    norm_num
  rw [hr]
  decide

end CFSG.Monster.Schur
