module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLModel
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.RootTransfer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLParabolic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLFlagMat
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.Module
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

open CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
  (slU slQAlpha slTorusDiag slQZero normalizer_slU exists_sylow_slU slQAlpha_le_of_parabolic
    mem_slQAlpha_iff slU_le_slQZero)
open scoped Matrix MatrixGroups

@[expose] noncomputable def slRootAlpha (k : ℕ) (hk : 2 ≤ k) (K : Type) [Field K] :
    SL(2, K) →* ↥(StatedSL k K) :=
  (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL k K).toMonoidHom.comp
    (CFSG.ClassicalInvolution.WeakCT.blockSL K k 2 0 (by omega))

theorem range_slRootAlpha_le_slQAlpha {k : ℕ} (hk : 2 ≤ k) {K : Type} [Field K] :
    (slRootAlpha k hk K).range ≤ slQAlpha k K := by
  rintro - ⟨A, rfl⟩
  rw [mem_slQAlpha_iff]
  intro i j hi hj
  change CFSG.ClassicalInvolution.Phan.blockMat k 0
      ((A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) i j = 0
  rw [CFSG.ClassicalInvolution.Phan.blockMat_apply_of_not_mem_left (ha := by omega)]
  exact Matrix.one_apply_ne (ne_of_gt hj)

theorem coe_slRootAlpha_torusSL {k : ℕ} (hk : 2 ≤ k) {K : Type} [Field K] (c : Kˣ) :
    (((slRootAlpha k hk K (torusSL c) : ↥(StatedSL k K)) : GL (Fin k) K) :
      Matrix (Fin k) (Fin k) K) = Matrix.diagonal (slTorusDiag k (c : K)) := by
  ext a b
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  change CFSG.ClassicalInvolution.Phan.blockMat k 0
      ((torusSL c : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) ⟨a, ha⟩ ⟨b, hb⟩ =
    Matrix.diagonal (slTorusDiag k (c : K)) ⟨a, ha⟩ ⟨b, hb⟩
  rw [Matrix.diagonal_apply]
  by_cases ha2 : a < 2
  · by_cases hb2 : b < 2
    · rw [CFSG.ClassicalInvolution.Phan.blockMat_apply,
        dif_pos (show (0 ≤ a ∧ a < 0 + 2) ∧ (0 ≤ b ∧ b < 0 + 2) from
          ⟨⟨Nat.zero_le _, by omega⟩, ⟨Nat.zero_le _, by omega⟩⟩)]
      interval_cases a <;> interval_cases b <;>
        simp [torusSL, slTorusDiag, Units.val_inv_eq_inv_val]
    · have hne : (⟨a, ha⟩ : Fin k) ≠ ⟨b, hb⟩ := by
        intro h
        have : a = b := by simpa [Fin.ext_iff] using h
        omega
      rw [CFSG.ClassicalInvolution.Phan.blockMat_apply_of_not_mem_right
          ((torusSL c : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) ⟨a, ha⟩
          (show ¬ (0 ≤ b ∧ b < 0 + 2) from by omega),
        Matrix.one_apply_ne hne, if_neg hne]
  · have ha0 : a ≠ 0 := by omega
    have ha1 : a ≠ 1 := by omega
    rw [CFSG.ClassicalInvolution.Phan.blockMat_apply_of_not_mem_left
        ((torusSL c : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
        (show ¬ (0 ≤ a ∧ a < 0 + 2) from by omega),
      Matrix.one_apply,
      show slTorusDiag k (c : K) (⟨a, ha⟩ : Fin k) = 1 from by
        simp [slTorusDiag, ha0, ha1]]

theorem slRootAlpha_torusSL_mem_normalizer {k : ℕ} (hk : 2 ≤ k) {K : Type} [Field K] (c : Kˣ) :
    slRootAlpha k hk K (torusSL c) ∈ Subgroup.normalizer (slU k K : Set ↥(StatedSL k K)) := by
  rw [normalizer_slU k K]
  refine Subgroup.mem_map_of_mem
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL k K).toMonoidHom ?_
  rw [LinearFlag.mem_upperTriangular]
  intro i j hij
  change (((slRootAlpha k hk K (torusSL c) : ↥(StatedSL k K)) : GL (Fin k) K) :
      Matrix (Fin k) (Fin k) K) i j = 0
  rw [coe_slRootAlpha_torusSL hk c]
  exact Matrix.diagonal_apply_ne _ (ne_of_gt hij)

theorem slRootAlpha_torusSL_mulVec {k : ℕ} [NeZero k] (hk : 2 ≤ k) {K : Type} [Field K]
    (c : Kˣ) :
    (((slRootAlpha k hk K (torusSL c) : ↥(StatedSL k K)) : GL (Fin k) K) :
      Matrix (Fin k) (Fin k) K) *ᵥ (Pi.single 0 1 : Fin k → K) = (c : K) • Pi.single 0 1 := by
  rw [coe_slRootAlpha_torusSL hk c]
  ext i
  rw [Matrix.mulVec_diagonal]
  by_cases hi : i = 0
  · subst hi
    simp [slTorusDiag]
  · rw [Pi.single_eq_of_ne hi, mul_zero, Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero]

theorem hasRootSL2_statedSL {k : ℕ} [NeZero k] (hk : 2 ≤ k) {K : Type} [Field K] [Finite K]
    [CharP K 2] : HasRootSL2 (StatedSL k K) (Pi.single 0 1) := by
  obtain ⟨U₀, hU⟩ := exists_sylow_slU (k := k) (K := K) (by omega : 1 ≤ k)
  refine hasRootSL2_of_leastParabolic (G := ↥(StatedSL k K)) (Γ := StatedSL k K)
    (e₀ := (Pi.single 0 (1 : K) : Fin k → K))
    (MulEquiv.refl ↥(StatedSL k K)) U₀ (slQAlpha k K) (slQZero k K)
    (slRootAlpha k hk K) ?_ ?_ ?_ ?_ ?_
  · exact Subgroup.map_id (slQZero k K)
  · rw [hU]
    exact slU_le_slQZero
  · intro P hP hUP hnot
    exact slQAlpha_le_of_parabolic hk hP (hU ▸ hUP) hnot
  · exact range_slRootAlpha_le_slQAlpha hk
  · intro c
    have hcoe : ((U₀ : Subgroup ↥(StatedSL k K)) : Set ↥(StatedSL k K)) =
        (slU k K : Set ↥(StatedSL k K)) := congrArg SetLike.coe hU
    refine ⟨?_, ?_⟩
    · rw [hcoe]
      exact slRootAlpha_torusSL_mem_normalizer hk c
    · exact slRootAlpha_torusSL_mulVec hk c

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr
