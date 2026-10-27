module

public import CFSG.ClassicalInvolution.WeakCT.SpinMinus6Generated

public section

namespace CFSG.RankThree.PartOne.CTP.SU4Even

open CliffordAlgebra QuadraticMap CFSG.LieType.RootSystem CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.CurtisTits CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
  CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

section Datum

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

theorem minusDatum_iSup_eq_top_three_even :
    ⨆ γ ∈ roots (isFiniteType_cartanB (3 - 1)) ∅, minusRootGroup 3 hirr γ = ⊤ := by
  refine eq_top_of_ker_le_of_range_le_map (spinAction (quadMinus 3 F b c)) ?_ ?_
  · have := isCentral_cliffordAlgebra_quadMinus 3 b c hirr
    rw [ker_spinAction_eq_bot_of_isCentral _ CharTwo.two_eq_zero]
    exact bot_le
  · rw [range_spinAction_quadMinus_three hirr]
    exact elementaryGroup_le_map_iSup_three hirr

theorem minusDatum_isCTGroupDatum_three_even :
    IsCTGroupDatum (coxeterMatrix (minusDatum 3 hirr).isFiniteType).toCoxeterSystem
      (weylAction (minusDatum 3 hirr).isFiniteType) (minusDatum 3 hirr).roots
      (minusDatum 3 hirr).rootGroup (minusWeyl 3 hirr) (minusTorus 3 hirr) where
  n_mem := minusDatum_n_mem 3 hirr
  conj_mem := minusDatum_conj_mem 3 hirr
  braid := minusDatum_braid 3 hirr
  H_le := minusDatum_H_le 3 hirr
  sq_mem := minusDatum_sq_mem 3 hirr
  H_conj_mem := minusDatum_H_conj_mem 3 hirr
  conj_H_mem := minusDatum_conj_H_mem 3 hirr
  le_rankOne := minusDatum_le_rankOne 3 hirr
  iSup_eq_top := minusDatum_iSup_eq_top_three_even hirr

theorem iSup_rankOne_minusDatum_three_even :
    ⨆ k : Fin (minusDatum 3 hirr).rank, rankOne (minusDatum 3 hirr).rootGroup k = ⊤ :=
  iSup_rankOne_eq_top_of_ct (D := minusDatum 3 hirr) (minusDatum_isCTGroupDatum_three_even hirr) rfl

theorem spinMinus6_blocks_sup_eq_top_even :
    haveI := fact_shortField hirr
    (minusLongBlock b c).range ⊔ (shortBlock hirr 3 finOne).range = ⊤ := by
  have := fact_shortField hirr
  rw [eq_top_iff, ← iSup_rankOne_minusDatum_three_even hirr]
  refine iSup_le fun k => ?_
  obtain ⟨k, hk⟩ := k
  have hk2 : k = 0 ∨ k = 1 := by
    change k < 3 - 1 at hk
    omega
  rcases hk2 with rfl | rfl
  · have hk0 : (0 : ℕ) + 1 < 3 - 1 := by norm_num
    exact (rankOne_minusDatum_long hirr (n := 3) (k := ⟨0, hk⟩) hk0).le.trans le_sup_left
  · have hk1 : ¬ (1 : ℕ) + 1 < 3 - 1 := by norm_num
    exact (rankOne_minusDatum_short hirr (n := 3) (k := ⟨1, hk⟩) hk1).le.trans le_sup_right

theorem spinMinusModel_blocks_sup_eq_top_even :
    haveI := fact_shortField hirr
    (spinMinusModel hirr).lb.range ⊔ (spinMinusModel hirr).sb.range = ⊤ :=
  spinMinus6_blocks_sup_eq_top_even hirr


end Datum

end CFSG.RankThree.PartOne.CTP.SU4Even
