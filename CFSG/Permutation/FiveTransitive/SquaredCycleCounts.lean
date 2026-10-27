module

public import CFSG.Permutation.FiveTransitive.PeriodRootCard
public import CFSG.Permutation.FiveTransitive.OddPowerCycleRoots

public section

namespace CFSG

namespace FiveTransitive.SquaredCycleCounts

open Equiv Function CyclePatternRoots OddPowerCycleRoots PeriodRootCard

variable {X : Type*} [Finite X]

theorem four_dvd_four_card (g : Perm X) : 4 ∣ Nat.card (FourRoot g) := by
  let e : FourRoot g ≃ PeriodRoot g 4 :=
    { toFun := fun x => ⟨x.val,(four_root_iff g x.val).mp x.property⟩
      invFun := fun x => ⟨x.val,(four_root_iff g x.val).mpr x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  exact period_dvd_card g 4

omit [Finite X] in
theorem two_square_eq_four_card (g : Perm X) :
    Nat.card (TwoRoot (g ^ 2)) = Nat.card (FourRoot g) := by
  let e : TwoRoot (g ^ 2) ≃ FourRoot g :=
    { toFun := fun x => ⟨x.val,x.property⟩
      invFun := fun x => ⟨x.val,x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Nat.card_congr e

theorem eight_dvd_four_square_card (g : Perm X) : 8 ∣ Nat.card (FourRoot (g ^ 2)) := by
  have hp (x : X) :
      ((g ^ 2) ((g ^ 2) ((g ^ 2) ((g ^ 2) x))) = x ∧
        (g ^ 2) ((g ^ 2) x) ≠ x) ↔ minimalPeriod g x = 8 := by
    constructor
    · rintro ⟨h8,h4⟩
      have hy : IsPeriodicPt g (2 ^ (2 + 1)) x := h8
      have hn : ¬ IsPeriodicPt g (2 ^ 2) x := h4
      exact minimalPeriod_eq_prime_pow hn hy
    · intro he
      have hy := isPeriodicPt_minimalPeriod g x
      rw [he] at hy
      refine ⟨hy, ?_⟩
      intro h4
      have hper : IsPeriodicPt g 4 x := h4
      have hd := hper.minimalPeriod_dvd
      rw [he] at hd
      norm_num at hd
  let e : FourRoot (g ^ 2) ≃ PeriodRoot g 8 :=
    { toFun := fun x => ⟨x.val,(hp x.val).mp x.property⟩
      invFun := fun x => ⟨x.val,(hp x.val).mpr x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  exact period_dvd_card g 8

end FiveTransitive.SquaredCycleCounts

end CFSG
