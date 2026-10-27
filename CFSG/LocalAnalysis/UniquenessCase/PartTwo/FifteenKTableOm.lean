module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKTableRot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKTablePlusSplit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKTableMinusSplit
public import CFSG.RankThree.PartOne.KF.ClsOmega

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.LieType.Universal.Spin

theorem s15k_table_omplus_rank {k : ℕ} (hk : 3 ≤ k) (z : Fin k ⊕ Fin k → ZMod 2) :
    2 ≤ CFSG.Open.pRank 3 (StatedOmega (StatedQuadPlus k (ZMod 2)) ⊓ s15kVecStab z) := by
  have h := s15k_table_rot_two (quadPlus k (ZMod 2)) (s15k_table_plus_pair hk z)
  rwa [coe_quadPlus] at h

theorem s15k_table_sp_rank {k : ℕ} (hk : 3 ≤ k) (z : Fin k ⊕ Fin k → ZMod 2) :
    2 ≤ CFSG.Open.pRank 3 (StatedSp k (ZMod 2) ⊓ s15kVecStab z) :=
  (s15k_table_omplus_rank hk z).trans (CFSG.SectionRank.pRank_mono (by norm_num)
    (inf_le_inf_right _ CFSG.RankThree.PartOne.KFU.statedOmega_quadPlus_le_statedSp))

theorem s15k_table_omminus_rank {k : ℕ} (hk : 3 ≤ k)
    (z : Fin (k - 1) ⊕ Fin (k - 1) ⊕ Fin 2 → ZMod 2) :
    1 ≤ CFSG.Open.pRank 3 (StatedOmega (StatedQuadMinus k (ZMod 2) 1 1) ⊓ s15kVecStab z) ∧
      (4 ≤ k → 2 ≤ CFSG.Open.pRank 3
        (StatedOmega (StatedQuadMinus k (ZMod 2) 1 1) ⊓ s15kVecStab z)) := by
  obtain ⟨h1, h2⟩ := s15k_table_minus_split hk z
  refine ⟨?_, fun h4 => ?_⟩
  · have h := s15k_table_rot_one _ h1
    rwa [coe_quadMinus] at h
  · have h := s15k_table_rot_two _ (h2 h4)
    rwa [coe_quadMinus] at h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
