module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusLat

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.StandardType

private lemma c2slomqmsf_simple_fst {l : ℕ} {t : Fin l} (h : t.val + 1 < l) :
    (omqMinusSimple l t).1 = Equiv.swap t ⟨t.val + 1, h⟩ := by
  unfold omqMinusSimple
  rw [dif_pos h]

private lemma c2slomqmsf_simple_snd {l : ℕ} {t : Fin l} (h : t.val + 1 < l) :
    (omqMinusSimple l t).2 = (1 : Fin l → ℤ) := by
  unfold omqMinusSimple
  rw [dif_pos h]

private lemma c2slomqmsf_simple_short_fst {l : ℕ} {t : Fin l} (h : ¬ t.val + 1 < l) :
    (omqMinusSimple l t).1 = (1 : Equiv.Perm (Fin l)) := by
  unfold omqMinusSimple
  rw [dif_neg h]

private lemma c2slomqmsf_simple_short_snd {l : ℕ} {t : Fin l} (h : ¬ t.val + 1 < l) :
    (omqMinusSimple l t).2 = spSgn t := by
  unfold omqMinusSimple
  rw [dif_neg h]

private lemma c2slomqmsf_flag_val {l j : ℕ} {t : Fin l} (ht : t.val ≠ j)
    (h : t.val + 1 < l) (b : Fin l) :
    (Equiv.swap t ⟨t.val + 1, h⟩ b).val ≤ j ↔ b.val ≤ j := by
  rw [Equiv.swap_apply_def]
  split_ifs with hb hb'
  · subst hb
    show b.val + 1 ≤ j ↔ b.val ≤ j
    omega
  · subst hb'
    show t.val ≤ j ↔ t.val + 1 ≤ j
    omega
  · rfl

private lemma c2slomqmsf_zero_val {l : ℕ} {t : Fin l} (h1 : 1 ≤ t.val)
    (h : t.val + 1 < l) (b : Fin l) :
    (Equiv.swap t ⟨t.val + 1, h⟩ b).val = 0 ↔ b.val = 0 := by
  rw [Equiv.swap_apply_def]
  split_ifs with hb hb'
  · subst hb
    simp only [false_iff]
    omega
  · subst hb'
    show t.val = 0 ↔ t.val + 1 = 0
    omega
  · rfl

theorem omq_minus_simpleFix_flag {l j : ℕ} (hj : j + 2 ≤ l) {t : Fin l} (ht : t.val ≠ j) :
    omqSignedActZ (omqMinusSimple l t).1 (omqMinusSimple l t).2 (omqMinusFlag l j) =
      omqMinusFlag l j := by
  funext b
  unfold omqSignedActZ omqMinusFlag
  by_cases h : t.val + 1 < l
  · rw [c2slomqmsf_simple_fst h, c2slomqmsf_simple_snd h]
    simp only [Pi.one_apply, one_mul]
    rw [Equiv.symm_swap]
    have hiff := c2slomqmsf_flag_val ht h b
    by_cases hb : b.val ≤ j
    · rw [if_pos hb, if_pos (hiff.mpr hb)]
    · rw [if_neg hb, if_neg (fun hh => hb (hiff.mp hh))]
  · rw [c2slomqmsf_simple_short_fst h, c2slomqmsf_simple_short_snd h]
    have hb1 : (1 : Equiv.Perm (Fin l)).symm b = b := by simp [Equiv.Perm.one_def]
    rw [hb1]
    by_cases hbt : b = t
    · rw [hbt]
      have htj : ¬ t.val ≤ j := by
        have htl : t.val = l - 1 := by
          have hlt : t.val < l := t.isLt
          omega
        omega
      simp [spSgn, htj]
    · have hsp : spSgn t b = 1 := by simp [spSgn, hbt]
      rw [hsp, one_mul]

theorem omq_minus_simpleFix_cube {l : ℕ} {t : Fin l} (ht : t.val + 1 < l) :
    omqSignedActZ (omqMinusSimple l t).1 (omqMinusSimple l t).2 (omqMinusCube l) =
      omqMinusCube l := by
  rw [c2slomqmsf_simple_fst ht, c2slomqmsf_simple_snd ht]
  funext b
  unfold omqSignedActZ omqMinusCube
  simp only [Pi.one_apply, one_mul]

theorem omq_minus_simpleFix_two_one_one {l : ℕ} {t : Fin l} (h1 : 1 ≤ t.val)
    (ht : t.val + 1 < l) :
    omqSignedActZ (omqMinusSimple l t).1 (omqMinusSimple l t).2
        (fun b : Fin l => if b.val = 0 then 2 else 1) =
      fun b : Fin l => if b.val = 0 then 2 else 1 := by
  rw [c2slomqmsf_simple_fst ht, c2slomqmsf_simple_snd ht]
  funext b
  unfold omqSignedActZ
  simp only [Pi.one_apply, one_mul]
  rw [Equiv.symm_swap]
  have hiff := c2slomqmsf_zero_val h1 ht b
  by_cases hb : b.val = 0
  · rw [if_pos hb, if_pos (hiff.mpr hb)]
  · rw [if_neg hb, if_neg (fun hh => hb (hiff.mp hh))]

end CFSG.LocalAnalysis.WeakClosure81
