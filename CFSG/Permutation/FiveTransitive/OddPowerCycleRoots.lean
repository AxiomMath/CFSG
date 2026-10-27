module

public import CFSG.Permutation.FiveTransitive.CyclePatternRoots
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.SetTheory.Cardinal.NatCard

public section

namespace CFSG

namespace FiveTransitive.OddPowerCycleRoots

open Equiv Function CyclePatternRoots

variable {X : Type*}

theorem two_root_iff (g : Perm X) (x : X) :
    (g (g x) = x ∧ g x ≠ x) ↔ minimalPeriod g x = 2 := by
  constructor
  · rintro ⟨h2,h1⟩
    have hp : IsPeriodicPt g 2 x := h2
    exact minimalPeriod_eq_prime hp h1
  · intro h
    constructor
    · have hp := isPeriodicPt_minimalPeriod g x
      rw [h] at hp
      exact hp
    · intro hf
      have hp : IsPeriodicPt g 1 x := hf
      have hd := hp.minimalPeriod_dvd
      rw [h] at hd
      norm_num at hd

theorem four_root_iff (g : Perm X) (x : X) :
    (g (g (g (g x))) = x ∧ g (g x) ≠ x) ↔ minimalPeriod g x = 4 := by
  constructor
  · rintro ⟨h4,h2⟩
    have hp : IsPeriodicPt g (2 ^ (1 + 1)) x := h4
    have hn : ¬ IsPeriodicPt g (2 ^ 1) x := h2
    exact minimalPeriod_eq_prime_pow hn hp
  · intro h
    constructor
    · have hp := isPeriodicPt_minimalPeriod g x
      rw [h] at hp
      exact hp
    · intro hf
      have hp : IsPeriodicPt g 2 x := hf
      have hd := hp.minimalPeriod_dvd
      rw [h] at hd
      norm_num at hd

private theorem minimalPeriod_pow_of_coprime (g : Perm X) (x : X) {t : ℕ}
    (ht : t ≠ 0) (hc : (minimalPeriod g x).Coprime t) :
    minimalPeriod (g ^ t) x = minimalPeriod g x := by
  rw [← g.iterate_eq_pow, minimalPeriod_iterate_eq_div_gcd ht, hc.gcd_eq_one,
    Nat.div_one]

theorem two_root_pow (g : Perm X) {t : ℕ} (ht : Odd t) (x : TwoRoot g) :
    (g ^ t) ((g ^ t) x.val) = x.val ∧ (g ^ t) x.val ≠ x.val := by
  apply (two_root_iff (g ^ t) x.val).mpr
  have hp := (two_root_iff g x.val).mp x.property
  have hc : (minimalPeriod g x.val).Coprime t := by
    rw [hp]
    exact ht.coprime_two_right.symm
  rw [minimalPeriod_pow_of_coprime g x.val (by obtain ⟨k,hk⟩ := ht; omega) hc, hp]

private theorem four_root_pow (g : Perm X) {t : ℕ} (ht : Odd t) (x : FourRoot g) :
    (g ^ t) ((g ^ t) ((g ^ t) ((g ^ t) x.val))) = x.val ∧
      (g ^ t) ((g ^ t) x.val) ≠ x.val := by
  apply (four_root_iff (g ^ t) x.val).mpr
  have hp := (four_root_iff g x.val).mp x.property
  have hc : (minimalPeriod g x.val).Coprime t := by
    rw [hp]
    exact ht.coprime_two_right.symm.pow_left 2
  rw [minimalPeriod_pow_of_coprime g x.val (by obtain ⟨k,hk⟩ := ht; omega) hc, hp]

theorem four_card_pow_pos [Finite X] (g : Perm X) {t : ℕ} (ht : Odd t)
    (h4 : 0 < Nat.card (FourRoot g)) : 0 < Nat.card (FourRoot (g ^ t)) := by
  obtain ⟨x⟩ : Nonempty (FourRoot g) := Finite.card_pos_iff.mp h4
  exact Finite.card_pos_iff.mpr ⟨⟨x.val, four_root_pow g ht x⟩⟩

end FiveTransitive.OddPowerCycleRoots

end CFSG
