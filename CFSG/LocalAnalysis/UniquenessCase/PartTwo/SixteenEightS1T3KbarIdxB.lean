module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarIdxA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarIdxBA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParSpN
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParON
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKJPrimeLie
public import CFSG.Open.StatedZModTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup

theorem s16t3_normIdx_sl {K : Type} [Field K] (hK : Nat.card K = 2) (n : ℕ) :
    s16t3_normIdx (StatedSL n K) := by
  rw [CFSG.Open.StatedAPI.statedSL_eq_top_of_card_two hK n]
  intro M₁ M₂ M₃ _ _ _
  exact Or.inl trivial

theorem s16t3_normIdx_sp {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (m : ℕ) :
    s16t3_normIdx (StatedSp m K) := by
  intro M₁ M₂ M₃ h₁ h₂ _
  exact Or.inl (Subgroup.mul_mem _
    (Subgroup.inv_mem _ (s16t3_sp_self_norm hK m h₁)) (s16t3_sp_self_norm hK m h₂))

theorem s16t3_normIdx_omplus {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ}
    (hm : 3 ≤ m) : s16t3_normIdx (StatedOmega (StatedQuadPlus m K)) := by
  have hidx : (⁅CFSG.MatrixModel.isometryCore (StatedQuadPlus m K),
      CFSG.MatrixModel.isometryCore (StatedQuadPlus m K)⁆.subgroupOf
      (CFSG.MatrixModel.isometryCore (StatedQuadPlus m K))).index = 2 := by
    have h := s15k_jp_commutator_index_plus hm hK
    rwa [← s15k_jp_subgroupOf_commutator
      (CFSG.MatrixModel.isometryCore (StatedQuadPlus m K))] at h
  refine s16t3_normIdx_of_index_le_two ?_
  have hNO : Subgroup.normalizer (StatedOmega (StatedQuadPlus m K) :
      Set (GL (Fin m ⊕ Fin m) K)) ≤ CFSG.MatrixModel.isometryCore (StatedQuadPlus m K) :=
    fun M hM => Subgroup.subset_closure (s16t3_omplus_isom hK hm hM)
  have hrel : (StatedOmega (StatedQuadPlus m K)).relIndex
      (CFSG.MatrixModel.isometryCore (StatedQuadPlus m K)) = 2 := hidx
  have h1 := Subgroup.relIndex_le_of_le_right (H := StatedOmega (StatedQuadPlus m K)) hNO
    (by rw [hrel]; norm_num)
  rw [hrel] at h1
  exact h1

theorem s16t3_normIdx_omminus {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ}
    (hm : 3 ≤ m) {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    s16t3_normIdx (StatedOmega (StatedQuadMinus m K b c)) := by
  have hidx : (⁅CFSG.MatrixModel.isometryCore (StatedQuadMinus m K b c),
      CFSG.MatrixModel.isometryCore (StatedQuadMinus m K b c)⁆.subgroupOf
      (CFSG.MatrixModel.isometryCore (StatedQuadMinus m K b c))).index = 2 := by
    have h := s15k_jp_commutator_index_minus (by omega : 2 ≤ m) hK hbc
    rwa [← s15k_jp_subgroupOf_commutator
      (CFSG.MatrixModel.isometryCore (StatedQuadMinus m K b c))] at h
  refine s16t3_normIdx_of_index_le_two ?_
  have hNO : Subgroup.normalizer (StatedOmega (StatedQuadMinus m K b c) :
      Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)) ≤
      CFSG.MatrixModel.isometryCore (StatedQuadMinus m K b c) :=
    fun M hM => Subgroup.subset_closure (s16t3_omminus_isom hK hm hbc hM)
  have hrel : (StatedOmega (StatedQuadMinus m K b c)).relIndex
      (CFSG.MatrixModel.isometryCore (StatedQuadMinus m K b c)) = 2 := hidx
  have h1 := Subgroup.relIndex_le_of_le_right (H := StatedOmega (StatedQuadMinus m K b c)) hNO
    (by rw [hrel]; norm_num)
  rw [hrel] at h1
  exact h1

theorem s16t3_normIdx_omminus_four {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    s16t3_normIdx (StatedOmega (StatedQuadMinus 2 K b c)) := by
  have hidx : (⁅CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c),
      CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c)⁆.subgroupOf
      (CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c))).index = 2 := by
    have h := s15k_jp_commutator_index_minus (by omega : 2 ≤ 2) hK hbc
    rwa [← s15k_jp_subgroupOf_commutator
      (CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c))] at h
  refine s16t3_normIdx_of_index_le_two ?_
  have hNO : Subgroup.normalizer (StatedOmega (StatedQuadMinus 2 K b c) :
      Set (GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K)) ≤
      CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c) :=
    s16t3_normalizer_omminus_four_le hK hbc
  have hrel : (StatedOmega (StatedQuadMinus 2 K b c)).relIndex
      (CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c)) = 2 := hidx
  have h1 := Subgroup.relIndex_le_of_le_right (H := StatedOmega (StatedQuadMinus 2 K b c)) hNO
    (by rw [hrel]; norm_num)
  rw [hrel] at h1
  exact h1

theorem s16t3_normIdx_alt {n : ℕ} (hn : 5 ≤ n) :
    s16t3_normIdx (alternatingGroup (Fin n)) := by
  haveI : Nontrivial (Fin n) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_fin]; omega)
  intro M₁ M₂ M₃ _ _ _
  exact CFSG.Quasithin.S15223.mem_of_index_le_two
    (by simpa using (alternatingGroup.index_eq_two (α := Fin n)).le) M₁ M₂ M₃

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
