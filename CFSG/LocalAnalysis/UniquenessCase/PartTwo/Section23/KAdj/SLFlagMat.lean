module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
open Matrix

variable {k : ℕ} {K : Type} [Field K]

private lemma slMat_eq_symm_B01 (g : ↥(StatedSL k K)) :
    slMat g =
      (((specialLinearGroupEquivStatedSL k K).symm g :
          Matrix.SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) := by
  conv_lhs => rw [← MulEquiv.apply_symm_apply (specialLinearGroupEquivStatedSL k K) g]
  exact specialLinearGroupEquivStatedSL_coe k K _

private lemma map_flagSpace_eq_iff_B01 {M : Matrix (Fin k) (Fin k) K} (hM : IsUnit M) (c : ℕ) :
    (LinearFlag.flagSpace k K c).map M.mulVecLin = LinearFlag.flagSpace k K c ↔
      ∀ i j : Fin k, c ≤ (i : ℕ) → (j : ℕ) < c → M i j = 0 := by
  constructor
  · intro h i j hic hjc
    have he : (Pi.single j (1 : K) : Fin k → K) ∈ LinearFlag.flagSpace k K c := by
      rw [LinearFlag.mem_flagSpace]
      intro m hm
      rw [Pi.single_eq_of_ne (by rintro rfl; omega : m ≠ j)]
    have hmem : M *ᵥ (Pi.single j (1 : K) : Fin k → K) ∈ LinearFlag.flagSpace k K c := by
      rw [← h]
      exact Submodule.mem_map_of_mem he
    have hz := (LinearFlag.mem_flagSpace.mp hmem) i hic
    rwa [Matrix.mulVec_single_one, Matrix.col_apply] at hz
  · intro h
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro x ⟨v, hv, rfl⟩
      rw [LinearFlag.mem_flagSpace]
      intro i hi
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_apply_eq_sum]
      exact Finset.sum_eq_zero fun j _ => by
        by_cases hjc : (j : ℕ) < c
        · rw [h i j hi hjc, zero_mul]
        · rw [LinearFlag.mem_flagSpace.mp hv j (not_lt.mp hjc), mul_zero]
    · exact (Submodule.equivMapOfInjective M.mulVecLin
        (Matrix.mulVec_injective_iff_isUnit.mpr hM) (LinearFlag.flagSpace k K c)).finrank_eq.symm

theorem mem_slU_iff {g : ↥(StatedSL k K)} :
    g ∈ slU k K ↔ (∀ i j : Fin k, j < i → slMat g i j = 0) ∧ ∀ i : Fin k, slMat g i i = 1 := by
  unfold slU
  rw [Subgroup.mem_map_equiv, LinearFlag.mem_unitriangular, slMat_eq_symm_B01 g]

theorem mem_slQAlpha_iff {g : ↥(StatedSL k K)} :
    g ∈ slQAlpha k K ↔ ∀ i j : Fin k, 2 ≤ (i : ℕ) → j < i → slMat g i j = 0 := by
  have hu : IsUnit (((specialLinearGroupEquivStatedSL k K).symm g :
      Matrix.SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) := by
    rw [Matrix.isUnit_iff_isUnit_det, ((specialLinearGroupEquivStatedSL k K).symm g).2]
    exact isUnit_one
  unfold slQAlpha
  rw [Subgroup.mem_map_equiv, LinearFlag.mem_flagStabilizer]
  constructor
  · intro h i j hi hj
    have hmem : (specialLinearGroupEquivStatedSL k K).symm g ∈
        LinearFlag.stabilizer (LinearFlag.flagSpace k K (i : ℕ)) :=
      h (i : ℕ) ⟨hi, i.isLt⟩
    have h2 := (map_flagSpace_eq_iff_B01 hu (i : ℕ)).mp (by
      rwa [LinearFlag.mem_stabilizer] at hmem)
    rw [slMat_eq_symm_B01 g]
    exact h2 i j le_rfl (by simpa only [Fin.lt_def] using hj)
  · intro h
    intro c hc
    rw [LinearFlag.mem_stabilizer]
    exact (map_flagSpace_eq_iff_B01 hu c).mpr fun i j hci hjc => by
      have hij : j < i := by
        rw [Fin.lt_def]
        exact lt_of_lt_of_le hjc hci
      have := h i j (le_trans hc.1 hci) hij
      rwa [slMat_eq_symm_B01 g] at this

theorem slU_le_slQZero [NeZero k] : slU k K ≤ slQZero k K := by
  intro g hg
  change ∃ c : K, slMat g *ᵥ (Pi.single 0 (1 : K) : Fin k → K) =
    c • (Pi.single 0 (1 : K) : Fin k → K)
  refine ⟨1, ?_⟩
  rw [one_smul]
  ext i
  rw [Matrix.mulVec_single_one, Matrix.col_apply]
  by_cases hi : i = 0
  · subst hi
    rw [Pi.single_eq_same]
    exact (mem_slU_iff.mp hg).2 0
  · rw [Pi.single_eq_of_ne hi,
      (mem_slU_iff.mp hg).1 i 0 ((Fin.pos_iff_ne_zero' i).mpr hi)]

theorem slMat_col_zero_of_mem_slQZero [NeZero k] {g : ↥(StatedSL k K)} (hg : g ∈ slQZero k K)
    (i : Fin k) (hi : i ≠ 0) : slMat g i 0 = 0 := by
  obtain ⟨c, hc⟩ := (mem_lineStab (Γ := StatedSL k K)
    (w₀ := (Pi.single 0 (1 : K) : Fin k → K))).mp hg
  have h := congrFun hc i
  rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, Pi.single_eq_of_ne hi,
    smul_zero] at h
  exact h

theorem slMat_lower_eq_zero_of_mem_inf [NeZero k] {g : ↥(StatedSL k K)}
    (hg : g ∈ slQAlpha k K ⊓ slQZero k K) (i j : Fin k) (hij : j < i) : slMat g i j = 0 := by
  rw [Subgroup.mem_inf] at hg
  by_cases h2 : 2 ≤ (i : ℕ)
  · exact (mem_slQAlpha_iff.mp hg.1) i j h2 hij
  · have hj0 : j = 0 := by
      apply Fin.ext
      have hi2 : (i : ℕ) < 2 := by omega
      have hij' : (j : ℕ) < (i : ℕ) := by simpa only [Fin.lt_def] using hij
      rw [show (j : ℕ) = 0 by omega, Fin.val_zero]
    subst hj0
    refine slMat_col_zero_of_mem_slQZero hg.2 i ?_
    rintro rfl
    exact absurd hij (lt_irrefl (0 : Fin k))

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
