module

public import CFSG.Permutation.FiveTransitive.OddPowerCycleRoots
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG

namespace FiveTransitive.OddPowerTwoCount

open Equiv Function CyclePatternRoots OddPowerCycleRoots

variable {X : Type*}

private theorem small_period {d t : ℕ} (ht : Odd t) (hpos : 0 < d) (hle : d ≤ 4)
    (hd : d ∣ 2 * t) (hn : ¬ d ∣ t) : d = 2 := by
  obtain ⟨k,hk⟩ := ht
  interval_cases d <;> omega

private theorem pow_apply_comm (g : Perm X) (t : ℕ) (x : X) :
    (g ^ t) (g x) = g ((g ^ t) x) := by
  have h : g ^ t * g = g * g ^ t := (pow_succ g t).symm.trans (pow_succ' g t)
  exact congrArg (fun e : Perm X => e x) h

private def poweredTwoStep (g : Perm X) (t : ℕ) : TwoRoot (g ^ t) → TwoRoot (g ^ t) :=
  fun x => ⟨g x.val, by
    constructor
    · rw [pow_apply_comm, pow_apply_comm, x.property.1]
    · intro h
      apply x.property.2
      apply g.injective
      rw [← pow_apply_comm]
      exact h⟩

private theorem two_root_of_pow_small [Finite X] (g : Perm X) {t : ℕ} (ht : Odd t)
    (hcard : Nat.card (TwoRoot (g ^ t)) ≤ 4) (x : TwoRoot (g ^ t)) :
    g (g x.val) = x.val ∧ g x.val ≠ x.val := by
  classical
  let f := poweredTwoStep g t
  let _ : Fintype (TwoRoot (g ^ t)) := Fintype.ofFinite _
  have hc : Semiconj Subtype.val f g := fun _ => rfl
  have he : minimalPeriod f x = minimalPeriod g x.val := by
    apply minimalPeriod_eq_minimalPeriod_iff.mpr
    intro n
    change (f^[n] x = x) ↔ (g^[n] x.val = x.val)
    rw [← hc.iterate_right n x]
    exact Subtype.ext_iff
  have hle : minimalPeriod g x.val ≤ 4 := by
    rw [← he]
    exact (minimalPeriod_le_card (f := f) (x := x)).trans
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have h2t : IsPeriodicPt g (2 * t) x.val := by
    change g^[2 * t] x.val = x.val
    rw [g.iterate_eq_pow, Nat.mul_comm 2 t, pow_mul]
    exact x.property.1
  have hnt : ¬ IsPeriodicPt g t x.val := by
    simpa only [IsPeriodicPt, IsFixedPt, g.iterate_eq_pow] using x.property.2
  have hp : 0 < minimalPeriod g x.val := h2t.minimalPeriod_pos
    (by obtain ⟨k,hk⟩ := ht; omega)
  have hn : ¬ minimalPeriod g x.val ∣ t := by
    rwa [← isPeriodicPt_iff_minimalPeriod_dvd]
  apply (two_root_iff g x.val).mpr
  exact small_period ht hp hle h2t.minimalPeriod_dvd hn

private theorem two_card_eq_pow_of_le_four [Finite X] (g : Perm X) {t : ℕ} (ht : Odd t)
    (hcard : Nat.card (TwoRoot (g ^ t)) ≤ 4) :
    Nat.card (TwoRoot g) = Nat.card (TwoRoot (g ^ t)) := by
  let e : TwoRoot g ≃ TwoRoot (g ^ t) :=
    { toFun := fun x => ⟨x.val, two_root_pow g ht x⟩
      invFun := fun x => ⟨x.val, two_root_of_pow_small g ht hcard x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Nat.card_congr e

theorem two_card_eq_pow_of_two_or_four [Finite X] (g : Perm X) {t : ℕ} (ht : Odd t)
    (hcard : Nat.card (TwoRoot (g ^ t)) = 2 ∨ Nat.card (TwoRoot (g ^ t)) = 4) :
    Nat.card (TwoRoot g) = Nat.card (TwoRoot (g ^ t)) :=
  two_card_eq_pow_of_le_four g ht (by omega)

end FiveTransitive.OddPowerTwoCount

end CFSG
