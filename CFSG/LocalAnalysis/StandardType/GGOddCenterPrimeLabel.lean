module

public import CFSG.LocalAnalysis.StandardType.MarkingDict
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Arith

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier (torsBound tors_of_not_dvd)

@[expose] def GGOddCenterPrimeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ p ∣ lab.rank + 1 ∧ p ∣ 2 ^ lab.n - 1) ∨
    (lab.tag = .twA ∧ p ∣ lab.rank + 1 ∧ p ∣ 2 ^ lab.n + 1) ∨
    (lab.tag = .E6 ∧ p = 3 ∧ p ∣ 2 ^ lab.n - 1) ∨
    (lab.tag = .twE6 ∧ p = 3 ∧ p ∣ 2 ^ lab.n + 1) ∨
    (lab.tag = .B2der ∧ p = 3)

theorem torsBound_mark_eq_one_of_not_oddCenterPrimeLabel
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (h : ¬ GGOddCenterPrimeLabel p lab) :
    torsBound p (markTag lab) (markRank lab) (markChar lab) (markDeg lab) = 1 := by
  have hnp2 : ¬ p ∣ 2 := fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
  have hnp4 : ¬ p ∣ 4 := fun hd => hnp2 (hp.dvd_of_dvd_pow (by simpa using hd : p ∣ 2 ^ 2))
  have small : ∀ a : ℕ, a = 1 ∨ a = 2 ∨ a = 4 → ¬ p ∣ a := by
    rintro a (rfl | rfl | rfl)
    · exact hp.not_dvd_one
    · exact hnp2
    · exact hnp4
  have htors : ∀ {t : StatedLieTag} {n q f : ℕ},
      (¬ p ∣ (genericOrders t n q f).1) →
      (¬ p ∣ (genericOrders t n q f).2) →
      (¬ p ∣ (exceptionalOrders t n q f).1) →
      (¬ p ∣ (exceptionalOrders t n q f).2) → torsBound p t n q f = 1 := by
    intro t n q f ha hb hc hd
    unfold torsBound
    rw [tors_of_not_dvd ha, tors_of_not_dvd hb, tors_of_not_dvd hc, tors_of_not_dvd hd]
  have hexc : ∀ (t : StatedLieTag) (n f : ℕ),
      (¬ p ∣ (exceptionalOrders t n 2 f).1) ∧
      (¬ p ∣ (exceptionalOrders t n 2 f).2) := by
    intro t n f
    have hs :
        ((exceptionalOrders t n 2 f).1 = 1 ∨ (exceptionalOrders t n 2 f).1 = 2 ∨
          (exceptionalOrders t n 2 f).1 = 4) ∧
        ((exceptionalOrders t n 2 f).2 = 1 ∨ (exceptionalOrders t n 2 f).2 = 2 ∨
          (exceptionalOrders t n 2 f).2 = 4) := by
      unfold exceptionalOrders
      split <;> simp_all
    exact ⟨small _ hs.1, small _ hs.2⟩
  have hchar2 : ∀ (t : StatedLieTag) (n f : ℕ),
      (¬ p ∣ (genericOrders t n 2 f).1) →
      (¬ p ∣ (genericOrders t n 2 f).2) → torsBound p t n 2 f = 1 := by
    intro t n f ha hb
    exact htors ha hb (hexc t n f).1 (hexc t n f).2
  obtain ⟨t, r, f⟩ := lab
  cases t
  · apply hchar2
    · intro hd
      have hdg := Nat.dvd_gcd_iff.mp hd
      exact h (Or.inl ⟨rfl, hdg.1, hdg.2⟩)
    · exact hp.not_dvd_one
  · apply hchar2
    · intro hd
      have hdg := Nat.dvd_gcd_iff.mp hd
      exact h (Or.inr (Or.inl ⟨rfl, hdg.1, hdg.2⟩))
    · exact hp.not_dvd_one
  · exact hchar2 .PSp r f (fun hd => hnp2 (hd.trans (Nat.gcd_dvd_left _ _))) hp.not_dvd_one
  · exact hchar2 .PSp r f (fun hd => hnp2 (hd.trans (Nat.gcd_dvd_left _ _))) hp.not_dvd_one
  · by_cases hr : r = 3
    · subst r
      exact hchar2 .PSL 4 f (fun hd => hnp4 (hd.trans (Nat.gcd_dvd_left _ _))) hp.not_dvd_one
    · simp only [markTag, markRank, markChar, markDeg, if_neg hr]
      apply hchar2
      · simp only [genericOrders]
        split_ifs
        · exact hp.not_dvd_one
        · exact hnp2
        · exact fun hd => hnp4 (hd.trans (Nat.gcd_dvd_left _ _))
      · simp only [genericOrders]
        split_ifs
        · exact hp.not_dvd_one
        · exact hnp2
        · exact hp.not_dvd_one
  · by_cases hr2 : r = 2
    · subst r
      exact hchar2 .PSL 2 (2 * f) (fun hd => hnp2 (hd.trans (Nat.gcd_dvd_left _ _))) hp.not_dvd_one
    · by_cases hr3 : r = 3
      · subst r
        simp only [markTag, markRank, markChar, markDeg, if_neg (by decide : (3 : ℕ) ≠ 2)]
        exact hchar2 .PSU 4 f (fun hd => hnp4 (hd.trans (Nat.gcd_dvd_left _ _))) hp.not_dvd_one
      · simp only [markTag, markRank, markChar, markDeg, if_neg hr2, if_neg hr3]
        exact hchar2 .POmegaMinus r f (fun hd => hnp4 (hd.trans (Nat.gcd_dvd_left _ _))) hp.not_dvd_one
  · apply hchar2
    · intro hd
      have hdg := Nat.dvd_gcd_iff.mp hd
      have hp3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdg.1
      exact h (Or.inr (Or.inr (Or.inl ⟨rfl, hp3, hdg.2⟩)))
    · exact hp.not_dvd_one
  · apply hchar2
    · exact fun hd => hnp2 (hd.trans (Nat.gcd_dvd_left _ _))
    · exact hp.not_dvd_one
  · exact hchar2 .E8 0 f hp.not_dvd_one hp.not_dvd_one
  · exact hchar2 .F4 0 f hp.not_dvd_one hp.not_dvd_one
  · apply hchar2
    · intro hd
      have hdg := Nat.dvd_gcd_iff.mp hd
      have hp3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdg.1
      exact h (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hp3, hdg.2⟩))))
    · exact hp.not_dvd_one
  · exact hchar2 .trialityD4 0 f hp.not_dvd_one hp.not_dvd_one
  · exact hchar2 .G2 0 f hp.not_dvd_one hp.not_dvd_one
  · exact hchar2 .twistedB2 0 f hp.not_dvd_one hp.not_dvd_one
  · exact hchar2 .twistedF4 0 f hp.not_dvd_one hp.not_dvd_one
  · have hp3 : p ≠ 3 := fun he =>
      h (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, he⟩))))
    have hnp3 : ¬ p ∣ 3 := fun hd =>
      hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd)
    change torsBound p .PSL 2 3 2 = 1
    unfold torsBound
    have hg : genericOrders .PSL 2 3 2 = (2, 1) := by norm_num [genericOrders]
    have he : exceptionalOrders .PSL 2 3 2 = (3, 1) := rfl
    rw [hg, he]
    simp only [tors_of_not_dvd hnp2, tors_of_not_dvd hnp3,
      tors_of_not_dvd hp.not_dvd_one, mul_one]
  · change torsBound p .PSU 3 3 1 = 1
    unfold torsBound
    have hg : genericOrders .PSU 3 3 1 = (1, 1) := by norm_num [genericOrders]
    have he : exceptionalOrders .PSU 3 3 1 = (1, 1) := rfl
    rw [hg, he]
    simp only [tors_of_not_dvd hp.not_dvd_one, mul_one]
  · exact hchar2 .Tits 0 f hp.not_dvd_one hp.not_dvd_one

end CFSG.StandardType

end
