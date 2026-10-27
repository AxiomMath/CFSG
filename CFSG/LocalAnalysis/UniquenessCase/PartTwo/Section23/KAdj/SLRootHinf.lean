module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
import CFSG.RankThree.PartTwo.Sec18.Components
public import CFSG.Adapters.SpecialLinearPerfect

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)
open scoped commutatorElement

variable {k : ℕ} {K : Type} [Field K]

theorem slRoot_le_slQZero [NeZero k] (hk : 3 ≤ k) : slRoot k hk K ≤ slQZero k K := by
  rintro _ ⟨A, rfl⟩
  rw [CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD.mem_lineStab]
  refine ⟨1, ?_⟩
  have hmat : ((slRootEmb k hk K A : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) =
      CFSG.ClassicalInvolution.Phan.blockMat k 1 (A : Matrix (Fin 2) (Fin 2) K) := rfl
  rw [hmat, one_smul]
  ext a
  rw [Matrix.mulVec_single_one, Matrix.col_apply,
    CFSG.ClassicalInvolution.Phan.blockMat_apply_of_not_mem_right _ _ (by simp)]
  simp [Matrix.one_apply, Pi.single_apply]

theorem commutator_slRoot_eq_self [Finite K] (hk : 3 ≤ k) (hK : 4 ≤ Nat.card K) :
    ⁅slRoot k hk K, slRoot k hk K⁆ = slRoot k hk K := by
  unfold slRoot
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator]
  have h : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  rw [Group.isPerfect_def] at h
  have h' : ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)), ⊤⁆ = ⊤ := h
  rw [h']

theorem slRoot_le_hinf [NeZero k] [Finite K] (hk : 3 ≤ k) (hK : 4 ≤ Nat.card K) :
    slRoot k hk K ≤ Hinf (slQZero k K) :=
  CFSG.RankThree.PartTwo.Sec18.le_inSubgroup_perfectResidual
    (commutator_slRoot_eq_self hk hK) (slRoot_le_slQZero hk)

theorem isSLn_slRoot [Finite K] (hk : 3 ≤ k) {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    IsSLn ↥(slRoot k hk K) 2 n := by
  refine ⟨K, inferInstance, inferInstance, hK, ⟨?_⟩⟩
  exact (MonoidHom.ofInjective (slRootEmb_injective hk)).symm.trans
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE