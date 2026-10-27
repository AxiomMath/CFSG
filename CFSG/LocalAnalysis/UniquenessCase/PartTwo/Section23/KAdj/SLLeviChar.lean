module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLModel
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLFlagMat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Open

variable {k : ℕ} {K : Type} [Field K]

private lemma slMat_mul_apply_self_B02 {q q' : ↥(StatedSL k K)}
    (hq : q ∈ slQAlpha k K) (hq' : q' ∈ slQAlpha k K) (j : Fin k) (hj : 2 ≤ (j : ℕ)) :
    slMat (q * q') j j = slMat q j j * slMat q' j j := by
  have hmul : slMat (q * q') = slMat q * slMat q' := by
    show (((q * q' : ↥(StatedSL k K)) : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) =
      (((q : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)) *
        (((q' : GL (Fin k) K) : Matrix (Fin k) (Fin k) K))
    rw [Subgroup.coe_mul, Units.val_mul]
  rw [hmul, Matrix.mul_apply]
  refine Finset.sum_eq_single j ?_ ?_
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with h | h
    · rw [mem_slQAlpha_iff.1 hq j l hj h, zero_mul]
    · rw [mem_slQAlpha_iff.1 hq' l j (le_trans hj (Nat.le_of_lt h)) h, mul_zero]
  · intro hjnot
    exact absurd (Finset.mem_univ j) hjnot

private noncomputable def levi_char_B02 (j : Fin k) (hj : 2 ≤ (j : ℕ)) :
    ↥(slQAlpha k K) →* Kˣ :=
  ({ toFun := fun q => slMat q.1 j j
     map_one' := by simp [slMat]
     map_mul' := fun q q' => slMat_mul_apply_self_B02 q.2 q'.2 j hj } :
    ↥(slQAlpha k K) →* K).toHomUnits

theorem slMat_diag_eq_one_of_mem_hinf [Finite K] {t : ↥(StatedSL k K)}
    (ht : t ∈ Hinf (slQAlpha k K)) (j : Fin k) (hj : 2 ≤ (j : ℕ)) : slMat t j j = 1 := by
  let χ : ↥(slQAlpha k K) →* Kˣ := levi_char_B02 j hj
  have hker : CFSG.perfectResidual ↥(slQAlpha k K) ≤ χ.ker := by
    refine le_trans (iInf_le (fun n : ℕ => derivedSeries ↥(slQAlpha k K) n) 1) ?_
    rw [derivedSeries_one]
    exact Abelianization.commutator_subset_ker χ
  unfold Hinf CFSG.inSubgroup at ht
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 ht
  have hvm : (χ m : K) = 1 := by
    simpa using congrArg Units.val (MonoidHom.mem_ker.1 (hker hm))
  simpa [χ, levi_char_B02] using hvm

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
