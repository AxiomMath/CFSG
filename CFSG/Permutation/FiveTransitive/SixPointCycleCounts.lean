module

public import CFSG.Permutation.FiveTransitive.CyclePatternRoots
public import Mathlib.GroupTheory.Perm.Sign

public section

namespace CFSG

namespace FiveTransitive.SixPointCycleCounts

open Equiv CyclePatternRoots

private theorem fin_counts : ∀ g : Perm (Fin 6), g.sign = 1 →
    (0 < Fintype.card (FourRoot g) → Fintype.card (TwoRoot g) = 2) ∧
    (4 ≤ Fintype.card (TwoRoot g) → 2 ≤ Fintype.card (Function.fixedPoints g)) := by
  decide +kernel

private def twoEquiv {X Y : Type*} (e : X ≃ Y) (g : Perm X) :
    TwoRoot g ≃ TwoRoot (e.permCongrHom g) :=
  e.subtypeEquiv (by
    intro x
    change ((g ^ 2) x = x ∧ g x ≠ x) ↔
      (((e.permCongrHom g) ^ 2) (e x) = e x ∧ (e.permCongrHom g) (e x) ≠ e x)
    rw [← map_pow]
    simp)

private def fourEquiv {X Y : Type*} (e : X ≃ Y) (g : Perm X) :
    FourRoot g ≃ FourRoot (e.permCongrHom g) :=
  e.subtypeEquiv (by
    intro x
    change ((g ^ 4) x = x ∧ (g ^ 2) x ≠ x) ↔
      (((e.permCongrHom g) ^ 4) (e x) = e x ∧ ((e.permCongrHom g) ^ 2) (e x) ≠ e x)
    rw [← map_pow, ← map_pow]
    simp)

private def fixedEquiv {X Y : Type*} (e : X ≃ Y) (g : Perm X) :
    Function.fixedPoints g ≃ Function.fixedPoints (e.permCongrHom g) :=
  e.subtypeEquiv (by intro x; change (g x = x) ↔ _; simp [Function.IsFixedPt])

theorem counts {X : Type*} [Fintype X] [DecidableEq X]
    (hX : Fintype.card X = 6) (g : Perm X) (heven : g.sign = 1) :
    (0 < Nat.card (FourRoot g) → Nat.card (TwoRoot g) = 2) ∧
    (4 ≤ Nat.card (TwoRoot g) → 2 ≤ Nat.card (Function.fixedPoints g)) := by
  let e := Fintype.equivFinOfCardEq hX
  have h := fin_counts (e.permCongrHom g) ((Perm.sign_permCongr e g).trans heven)
  have htwo := Nat.card_congr (twoEquiv e g)
  have hfour := Nat.card_congr (fourEquiv e g)
  have hfixed := Nat.card_congr (fixedEquiv e g)
  simp only [Nat.card_eq_fintype_card] at htwo hfour hfixed ⊢
  rw [htwo, hfour, hfixed]
  exact h

end FiveTransitive.SixPointCycleCounts

end CFSG
