module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.OmegaPlusActOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
import CFSG.RankThree.PartTwo.Sec18.Components
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusFamData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)
open scoped MatrixGroups

private lemma commutator_range_eq_self_E07 {G H : Type} [Group G] [Group H] (f : G →* H)
    (hG : Group.IsPerfect G) : ⁅f.range, f.range⁆ = f.range := by
  haveI : Group.IsPerfect G := hG
  exact Subgroup.isPerfect_iff.mp (Group.IsPerfect.range f)

private lemma isSLn_range_E07 {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) {H : Type} [Group H] (f : SL(2, K) →* H)
    (hf : Function.Injective f) : IsSLn ↥f.range 2 n :=
  ⟨K, inferInstance, inferInstance, hK,
    ⟨(MonoidHom.ofInjective hf).symm.trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K)⟩⟩

theorem plusRootEmbTwo_range_le (K : Type) [Field K] [Finite K] [CharP K 2] :
    (plusRootEmbTwo K).range ≤ plusFlagStab K 3 ({1} : Finset ℕ) := by
  rintro _ ⟨A, rfl⟩
  exact plusResExt_iotaTwo_mem (r := 3) (t := 1) (D := {1}) le_rfl
    (show 1 + 2 = 3 from rfl) (fun d hd => by simp at hd; omega) A

theorem plusRootEmbOne_range_le (K : Type) [Field K] [Finite K] [CharP K 2] :
    (plusRootEmbOne K).range ≤ plusFlagStab K 3 ({1} : Finset ℕ) := by
  rintro _ ⟨A, rfl⟩
  exact plusResExt_iotaOne_mem (r := 3) (t := 1) (D := {1}) le_rfl
    (show 1 + 2 = 3 from rfl) (fun d hd => by simp at hd; omega) A

theorem plusRootEmbTwo_range_le_hinf {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) :
    (plusRootEmbTwo K).range ≤ Hinf (plusFlagStab K 3 ({1} : Finset ℕ)) := by
  have hperf : Group.IsPerfect (SL(2, K)) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  have hcomm : ⁅(plusRootEmbTwo K).range, (plusRootEmbTwo K).range⁆ =
      (plusRootEmbTwo K).range := commutator_range_eq_self_E07 (plusRootEmbTwo K) hperf
  exact CFSG.RankThree.PartTwo.Sec18.le_inSubgroup_perfectResidual hcomm
    (plusRootEmbTwo_range_le K)

theorem plusRootEmbOne_range_le_hinf {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) :
    (plusRootEmbOne K).range ≤ Hinf (plusFlagStab K 3 ({1} : Finset ℕ)) := by
  have hperf : Group.IsPerfect (SL(2, K)) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  have hcomm : ⁅(plusRootEmbOne K).range, (plusRootEmbOne K).range⁆ =
      (plusRootEmbOne K).range := commutator_range_eq_self_E07 (plusRootEmbOne K) hperf
  exact CFSG.RankThree.PartTwo.Sec18.le_inSubgroup_perfectResidual hcomm
    (plusRootEmbOne_range_le K)

theorem isSLn_plusRootEmbTwo_range {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) : IsSLn ↥(plusRootEmbTwo K).range 2 n :=
  isSLn_range_E07 hK (plusRootEmbTwo K) (plusRootEmbTwo_injective K)

theorem isSLn_plusRootEmbOne_range {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) : IsSLn ↥(plusRootEmbOne K).range 2 n :=
  isSLn_range_E07 hK (plusRootEmbOne K) (plusRootEmbOne_injective K)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
