module

import CFSG.GroupTheory.E3Params
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin

private theorem w183_index_eq_two_pow {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (x : MulAut W) :
    ∃ i : ℕ, (fixV (Subgroup.zpowers x)).index = 2 ^ i ∧
      E3.mQuot ⊤ (fixV (Subgroup.zpowers x)) = i := by
  refine ⟨rkIdx (fixV (Subgroup.zpowers x)), CFSG.Quasithin.B1.index_eq_two_pow hW _, ?_⟩
  exact CFSG.GroupTheory.mQuot_top_eq_rkIdx _

theorem le_mQuot_of_two_pow_le_index {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (x : MulAut W) {m : ℕ}
    (h : 2 ^ m ≤ (fixV (Subgroup.zpowers x)).index) :
    m ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers x)) := by
  obtain ⟨i, hi, hmq⟩ := w183_index_eq_two_pow hW x
  rw [hmq]
  rw [hi] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h

theorem lt_mQuot_of_two_pow_lt_index {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (x : MulAut W) {m : ℕ}
    (h : 2 ^ m < (fixV (Subgroup.zpowers x)).index) :
    m < E3.mQuot ⊤ (fixV (Subgroup.zpowers x)) := by
  obtain ⟨i, hi, hmq⟩ := w183_index_eq_two_pow hW x
  rw [hmq]
  rw [hi] at h
  exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h

end CFSG.LocalAnalysis.WeakClosure81
