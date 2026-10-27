module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangKGInputs
public import CFSG.LocalAnalysis.StandardType.MarkingDict
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Arith

public section

namespace CFSG.StandardType.KGUniv

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
  (torsBound tors tors_of_not_dvd genericOrders_snd_le)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)

private lemma not_dvd_of_dvd_two {p x : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hx : x ∣ 2) :
    ¬ p ∣ x :=
  fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (h.trans hx))

private lemma not_dvd_of_dvd_three {p x : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hx : x ∣ 3) :
    ¬ p ∣ x :=
  fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (h.trans hx))

private lemma not_dvd_of_dvd_four {p x : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hx : x ∣ 4) :
    ¬ p ∣ x := by
  intro h
  have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (n := 2) (by simpa using h.trans hx)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

private lemma not_dvd_of_mem_12 {p x : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hx : x = 1 ∨ x = 2) : ¬ p ∣ x := by
  rcases hx with rfl | rfl
  · exact hp.not_dvd_one
  · exact not_dvd_of_dvd_two hp hp2 (dvd_refl 2)

private lemma not_dvd_of_mem_124 {p x : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hx : x = 1 ∨ x = 2 ∨ x = 4) : ¬ p ∣ x := by
  rcases hx with rfl | rfl | rfl
  · exact hp.not_dvd_one
  · exact not_dvd_of_dvd_two hp hp2 (dvd_refl 2)
  · exact not_dvd_of_dvd_four hp hp2 (dvd_refl 4)

private lemma genericOrders_snd_mem (t : StatedLieTag) (n p f : ℕ) :
    (genericOrders t n p f).2 = 1 ∨ (genericOrders t n p f).2 = 2 := by
  obtain ⟨h1, h2⟩ := genericOrders_snd_le t n p f
  omega

private lemma exceptionalOrders_two (t : StatedLieTag) (n f : ℕ) :
    ((exceptionalOrders t n 2 f).1 = 1 ∨ (exceptionalOrders t n 2 f).1 = 2 ∨
        (exceptionalOrders t n 2 f).1 = 4) ∧
      ((exceptionalOrders t n 2 f).2 = 1 ∨ (exceptionalOrders t n 2 f).2 = 2 ∨
        (exceptionalOrders t n 2 f).2 = 4) := by
  unfold exceptionalOrders
  split <;> simp_all

private lemma genericOrders_PSL_fst_dvd (n p f : ℕ) :
    (genericOrders .PSL n p f).1 ∣ n := by
  simp only [genericOrders]
  exact Nat.gcd_dvd_left _ _

private lemma genericOrders_PSU_fst_dvd (n p f : ℕ) :
    (genericOrders .PSU n p f).1 ∣ n := by
  simp only [genericOrders]
  exact Nat.gcd_dvd_left _ _

private lemma genericOrders_PSp_fst_dvd (n p f : ℕ) :
    (genericOrders .PSp n p f).1 ∣ 2 := by
  simp only [genericOrders]
  exact Nat.gcd_dvd_left _ _

private lemma genericOrders_POmegaPlus_fst_dvd (n p f : ℕ) :
    (genericOrders .POmegaPlus n p f).1 ∣ 4 := by
  simp only [genericOrders]
  split_ifs <;> first | exact Nat.gcd_dvd_left _ _ | norm_num

private lemma genericOrders_POmegaMinus_fst_dvd (n p f : ℕ) :
    (genericOrders .POmegaMinus n p f).1 ∣ 4 := by
  simp only [genericOrders]
  exact Nat.gcd_dvd_left _ _

private lemma genericOrders_E6_fst_dvd (n p f : ℕ) :
    (genericOrders .E6 n p f).1 ∣ 3 := by
  simp only [genericOrders]
  exact Nat.gcd_dvd_left _ _

private lemma genericOrders_twistedE6_fst_dvd (n p f : ℕ) :
    (genericOrders .twistedE6 n p f).1 ∣ 3 := by
  simp only [genericOrders]
  exact Nat.gcd_dvd_left _ _

private lemma genericOrders_E7_fst_dvd (n p f : ℕ) :
    (genericOrders .E7 n p f).1 ∣ 2 := by
  simp only [genericOrders]
  exact Nat.gcd_dvd_left _ _

private lemma genericOrders_default_fst_eq_one {t : StatedLieTag}
    (ht : t = .E8 ∨ t = .F4 ∨ t = .G2 ∨ t = .trialityD4 ∨ t = .twistedF4) (n p f : ℕ) :
    (genericOrders t n p f).1 = 1 := by
  rcases ht with rfl | rfl | rfl | rfl | rfl <;> rfl

private lemma torsBound_eq_one {p : ℕ} {t : StatedLieTag} {n q f : ℕ}
    (ha : ¬ p ∣ (genericOrders t n q f).1) (hb : ¬ p ∣ (genericOrders t n q f).2)
    (hc : ¬ p ∣ (exceptionalOrders t n q f).1) (hd : ¬ p ∣ (exceptionalOrders t n q f).2) :
    torsBound p t n q f = 1 := by
  unfold torsBound
  rw [tors_of_not_dvd ha, tors_of_not_dvd hb, tors_of_not_dvd hc, tors_of_not_dvd hd]

theorem torsBound_mark_eq_one_of_regLabel {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hreg : GGNbrLangRegLabel p lab) :
    torsBound p (markTag lab) (markRank lab) (markChar lab) (markDeg lab) = 1 := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;>
    simp only [GGNbrLangRegLabel, GGNbrLangRegLinearLabel, GGNbrLangRegClassicalLabel,
      GGNbrLangRegExcLabel] at hreg
  ·
    simp at hreg
    simp only [markTag, markRank, markChar, markDeg]
    refine torsBound_eq_one ?_ ?_ ?_ ?_
    · exact fun h => hreg (h.trans (genericOrders_PSL_fst_dvd (l + 1) 2 n))
    · exact not_dvd_of_mem_12 hp hp2 (genericOrders_snd_mem _ _ _ _)
    · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).1
    · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).2
  ·
    simp at hreg
    simp only [markTag, markRank, markChar, markDeg]
    refine torsBound_eq_one ?_ ?_ ?_ ?_
    · exact fun h => hreg (h.trans (genericOrders_PSU_fst_dvd (l + 1) 2 n))
    · exact not_dvd_of_mem_12 hp hp2 (genericOrders_snd_mem _ _ _ _)
    · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).1
    · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).2
  ·
    simp only [markTag, markRank, markChar, markDeg]
    refine torsBound_eq_one ?_ ?_ ?_ ?_
    · exact not_dvd_of_dvd_two hp hp2 (genericOrders_PSp_fst_dvd l 2 n)
    · exact not_dvd_of_mem_12 hp hp2 (genericOrders_snd_mem _ _ _ _)
    · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).1
    · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).2
  ·
    simp only [markTag, markRank, markChar, markDeg]
    refine torsBound_eq_one ?_ ?_ ?_ ?_
    · exact not_dvd_of_dvd_two hp hp2 (genericOrders_PSp_fst_dvd l 2 n)
    · exact not_dvd_of_mem_12 hp hp2 (genericOrders_snd_mem _ _ _ _)
    · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).1
    · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).2
  ·
    by_cases hl : l = 3
    · simp only [markTag, markRank, markChar, markDeg, if_pos hl]
      refine torsBound_eq_one ?_ ?_ ?_ ?_
      · exact not_dvd_of_dvd_four hp hp2 (genericOrders_PSL_fst_dvd 4 2 n)
      · exact not_dvd_of_mem_12 hp hp2 (genericOrders_snd_mem _ _ _ _)
      · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).1
      · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).2
    · simp only [markTag, markRank, markChar, markDeg, if_neg hl]
      refine torsBound_eq_one ?_ ?_ ?_ ?_
      · exact not_dvd_of_dvd_four hp hp2 (genericOrders_POmegaPlus_fst_dvd l 2 n)
      · exact not_dvd_of_mem_12 hp hp2 (genericOrders_snd_mem _ _ _ _)
      · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).1
      · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).2
  ·
    by_cases hl2 : l = 2
    · simp only [markTag, markRank, markChar, markDeg, if_pos hl2]
      refine torsBound_eq_one ?_ ?_ ?_ ?_
      · exact not_dvd_of_dvd_two hp hp2 (genericOrders_PSL_fst_dvd 2 2 (2 * n))
      · exact not_dvd_of_mem_12 hp hp2 (genericOrders_snd_mem _ _ _ _)
      · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).1
      · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).2
    · by_cases hl3 : l = 3
      · simp only [markTag, markRank, markChar, markDeg, if_neg hl2, if_pos hl3]
        refine torsBound_eq_one ?_ ?_ ?_ ?_
        · exact not_dvd_of_dvd_four hp hp2 (genericOrders_PSU_fst_dvd 4 2 n)
        · exact not_dvd_of_mem_12 hp hp2 (genericOrders_snd_mem _ _ _ _)
        · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).1
        · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).2
      · simp only [markTag, markRank, markChar, markDeg, if_neg hl2, if_neg hl3]
        refine torsBound_eq_one ?_ ?_ ?_ ?_
        · exact not_dvd_of_dvd_four hp hp2 (genericOrders_POmegaMinus_fst_dvd l 2 n)
        · exact not_dvd_of_mem_12 hp hp2 (genericOrders_snd_mem _ _ _ _)
        · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).1
        · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).2
  ·
    simp at hreg
    simp only [markTag, markRank, markChar, markDeg]
    refine torsBound_eq_one ?_ ?_ ?_ ?_
    · exact not_dvd_of_dvd_three hp hreg (genericOrders_E6_fst_dvd 0 2 n)
    · exact not_dvd_of_mem_12 hp hp2 (genericOrders_snd_mem _ _ _ _)
    · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).1
    · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).2
  ·
    simp only [markTag, markRank, markChar, markDeg]
    refine torsBound_eq_one ?_ ?_ ?_ ?_
    · exact not_dvd_of_dvd_two hp hp2 (genericOrders_E7_fst_dvd 0 2 n)
    · exact not_dvd_of_mem_12 hp hp2 (genericOrders_snd_mem _ _ _ _)
    · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).1
    · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).2
  ·
    simp only [markTag, markRank, markChar, markDeg]
    refine torsBound_eq_one ?_ ?_ ?_ ?_
    · rw [genericOrders_default_fst_eq_one (Or.inl rfl) 0 2 n]
      exact hp.not_dvd_one
    · exact not_dvd_of_mem_12 hp hp2 (genericOrders_snd_mem _ _ _ _)
    · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).1
    · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).2
  ·
    simp only [markTag, markRank, markChar, markDeg]
    refine torsBound_eq_one ?_ ?_ ?_ ?_
    · rw [genericOrders_default_fst_eq_one (Or.inr (Or.inl rfl)) 0 2 n]
      exact hp.not_dvd_one
    · exact not_dvd_of_mem_12 hp hp2 (genericOrders_snd_mem _ _ _ _)
    · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).1
    · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).2
  ·
    simp at hreg
    simp only [markTag, markRank, markChar, markDeg]
    refine torsBound_eq_one ?_ ?_ ?_ ?_
    · exact not_dvd_of_dvd_three hp hreg (genericOrders_twistedE6_fst_dvd 0 2 n)
    · exact not_dvd_of_mem_12 hp hp2 (genericOrders_snd_mem _ _ _ _)
    · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).1
    · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).2
  ·
    simp only [markTag, markRank, markChar, markDeg]
    refine torsBound_eq_one ?_ ?_ ?_ ?_
    · rw [genericOrders_default_fst_eq_one (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) 0 2 n]
      exact hp.not_dvd_one
    · exact not_dvd_of_mem_12 hp hp2 (genericOrders_snd_mem _ _ _ _)
    · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).1
    · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).2
  ·
    simp only [markTag, markRank, markChar, markDeg]
    refine torsBound_eq_one ?_ ?_ ?_ ?_
    · rw [genericOrders_default_fst_eq_one (Or.inr (Or.inr (Or.inl rfl))) 0 2 n]
      exact hp.not_dvd_one
    · exact not_dvd_of_mem_12 hp hp2 (genericOrders_snd_mem _ _ _ _)
    · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).1
    · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).2
  ·
    simp at hreg
  ·
    simp only [markTag, markRank, markChar, markDeg]
    refine torsBound_eq_one ?_ ?_ ?_ ?_
    · rw [genericOrders_default_fst_eq_one (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) 0 2 n]
      exact hp.not_dvd_one
    · exact not_dvd_of_mem_12 hp hp2 (genericOrders_snd_mem _ _ _ _)
    · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).1
    · exact not_dvd_of_mem_124 hp hp2 (exceptionalOrders_two _ _ _).2
  ·
    simp at hreg
  ·
    simp at hreg
  ·
    simp at hreg

end CFSG.StandardType.KGUniv
