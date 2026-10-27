module

public import CFSG.Quasithin.H13.NQCatA314CentL35
public import CFSG.Quasithin.H13.NQCatT513U35Y

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open CFSG.Quasithin.H13.NQCat.T513.U35 CFSG.RankThree.PartOne.HNB Matrix
open CFSG.Quasithin.H13.KGU35 (f25Data suMat suMat_apply suMat_injective)
open CFSG.Quasithin.H13.KGAutSyl.U35Syl (RR)
open scoped commutatorElement

theorem RR4_eq_unitaryInvT : RR ^ 4 = CFSG.RankThree.Classical.unitaryInvT f25Data := by
  apply suMat_injective
  rw [suMat_RR4, suMat_apply, CFSG.RankThree.Classical.coe_unitaryInvT,
    CFSG.RankThree.Classical.negNegOneDiag]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem card_commutator_centralizer_su35 {w : ↥SU} (hw : orderOf w = 2) :
    Nat.card ↥⁅Subgroup.centralizer ({w} : Set ↥SU), Subgroup.centralizer ({w} : Set ↥SU)⁆ ≤
      120 := by
  have hc : IsConj (RR ^ 4) w := by
    rw [RR4_eq_unitaryInvT]
    exact CFSG.RankThree.Classical.isConj_unitaryInvT_of_orderOf f25Data (by norm_num) hw
  refine (card_commutator_centralizer_le_of_isConj hc).trans ?_
  have hle : ⁅Subgroup.centralizer ({RR ^ 4} : Set ↥SU),
      Subgroup.centralizer ({RR ^ 4} : Set ↥SU)⁆ ≤ Yhat := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    have bg := isBlk_of_comm (Subgroup.mem_centralizer_singleton_iff.mp hg)
    have bh := isBlk_of_comm (Subgroup.mem_centralizer_singleton_iff.mp hh)
    obtain ⟨bg', eg⟩ := isBlk_inv bg
    obtain ⟨bh', eh⟩ := isBlk_inv bh
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def, map_mul, map_mul, map_mul]
      exact ((bg.mul bh).1.mul bg').1.mul bh' |>.1
    · rw [commutatorElement_def, map_mul, map_mul, map_mul,
        ((bg.mul bh).1.mul bg').1.mul bh' |>.2, ((bg.mul bh).1.mul bg').2, (bg.mul bh).2]
      calc suMat g 2 2 * suMat h 2 2 * suMat g⁻¹ 2 2 * suMat h⁻¹ 2 2 =
          (suMat g⁻¹ 2 2 * suMat g 2 2) * (suMat h⁻¹ 2 2 * suMat h 2 2) := by ring
        _ = 1 := by rw [eg, eh, one_mul]
  exact (Subgroup.card_le_of_le hle).trans card_Yhat

theorem card_commutator_centralizer_pu35 {w : PU} (hw : orderOf w = 2) :
    Nat.card ↥⁅Subgroup.centralizer ({w} : Set PU), Subgroup.centralizer ({w} : Set PU)⁆ ≤
      120 := by
  have hc : IsConj z0 w := by
    have h1 := CFSG.RankThree.Classical.isConj_unitaryProj_unitaryInvT f25Data (by norm_num) hw
    rw [← RR4_eq_unitaryInvT] at h1
    exact h1.symm
  exact (card_commutator_centralizer_le_of_isConj hc).trans card_commutator_centralizer_z0

end CFSG.Quasithin.H13.NQCat.A314D
