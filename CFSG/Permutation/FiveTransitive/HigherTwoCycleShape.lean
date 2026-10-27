module

public import CFSG.Permutation.FiveTransitive.LocalEvenCycleShape
public import CFSG.Permutation.FiveTransitive.SquaredCycleCounts
public import CFSG.Permutation.FiveTransitive.TwoPowerPeriodWitness

public section

namespace CFSG

namespace FiveTransitive.HigherTwoCycleShape

open Equiv MulAction CyclePatternRoots SquaredCycleCounts

variable {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
  [FaithfulSMul G X]

omit [Finite G] [Fintype X] in
theorem order_toPerm (a : G) : orderOf (toPerm a : Perm X) = orderOf a := by
  apply orderOf_injective (toPermHom G X)
  intro u v h
  apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
  intro x
  exact DFunLike.congr_fun h x

theorem order_eight_shape
    (hlocal : SixLocalSylowExponentTwo.EvenSixLocal G X)
    (hinv : ∀ u : G, orderOf u = 2 →
      Nat.card (Function.fixedPoints (toPerm u : Perm X)) ≤ 6)
    (a : G) (ha : orderOf a = 8) :
    Nat.card (FourRoot (toPerm a : Perm X)) = 4 ∧
      Nat.card (TwoRoot (toPerm a : Perm X)) = 2 ∧
      Nat.card (Function.fixedPoints (toPerm a : Perm X)) = 0 := by
  let g := (toPerm a : Perm X)
  have ha2 : orderOf (a ^ 2) = 4 := by rw [orderOf_pow, ha]; norm_num
  have h4sq : 0 < Nat.card (FourRoot (toPerm (a ^ 2) : Perm X)) := by
    apply TwoPowerPeriodWitness.four_card_pos_of_order_four
    rw [order_toPerm, ha2]
  have hshape2 := LocalEvenCycleShape.two_power_shape hlocal hinv (a ^ 2) 2
    (by decide) ha2 h4sq
  have he2 : Nat.card (TwoRoot (toPerm (a ^ 2) : Perm X)) = Nat.card (FourRoot g) := by
    simpa only [g, ← toPermHom_apply, map_pow] using two_square_eq_four_card g
  rw [he2] at hshape2
  have hd4 := four_dvd_four_card g
  have hc4 : Nat.card (FourRoot g) = 4 := by omega
  have hshape := LocalEvenCycleShape.two_power_shape hlocal hinv a 3 (by decide)
    ha (by change 0 < Nat.card (FourRoot g); omega)
  have ha4 : orderOf (a ^ 4) = 2 := by rw [orderOf_pow, ha]; norm_num
  have hi := hinv (a ^ 4) ha4
  have hi' : Nat.card (Function.fixedPoints (g ^ 4 : Perm X)) ≤ 6 := by
    simpa only [g, ← toPermHom_apply, map_pow] using hi
  have hs1 := TwoElementFixedBound.fixed_square_card g
  have hs2 := TwoElementFixedBound.fixed_square_card (g ^ 2)
  rw [two_square_eq_four_card, ← pow_mul] at hs2
  change Nat.card (Function.fixedPoints (g ^ 2 : Perm X)) + Nat.card (FourRoot g) =
    Nat.card (Function.fixedPoints (g ^ 4 : Perm X)) at hs2
  change Nat.card (TwoRoot g) = 2 ∨ Nat.card (TwoRoot g) = 4 at hshape
  change Nat.card (FourRoot g) = 4 ∧ Nat.card (TwoRoot g) = 2 ∧
    Nat.card (Function.fixedPoints g) = 0
  exact ⟨hc4, by omega, by omega⟩

private theorem no_order_sixteen
    (hlocal : SixLocalSylowExponentTwo.EvenSixLocal G X)
    (hinv : ∀ u : G, orderOf u = 2 →
      Nat.card (Function.fixedPoints (toPerm u : Perm X)) ≤ 6)
    (a : G) : orderOf a ≠ 16 := by
  intro ha
  have ha2 : orderOf (a ^ 2) = 8 := by rw [orderOf_pow, ha]; norm_num
  have hs := (order_eight_shape hlocal hinv (a ^ 2) ha2).1
  have hd := eight_dvd_four_square_card (toPerm a : Perm X)
  have hs' : Nat.card (FourRoot ((toPerm a : Perm X) ^ 2)) = 4 := by
    simpa only [← toPermHom_apply, map_pow] using hs
  rw [hs'] at hd
  norm_num at hd

private theorem two_power_exponent_le_three
    (hlocal : SixLocalSylowExponentTwo.EvenSixLocal G X)
    (hinv : ∀ u : G, orderOf u = 2 →
      Nat.card (Function.fixedPoints (toPerm u : Perm X)) ≤ 6)
    (a : G) (k : ℕ) (ha : orderOf a = 2 ^ k) : k ≤ 3 := by
  by_contra hk
  have hk4 : 4 ≤ k := by omega
  have hd : 16 ∣ orderOf a := by
    rw [ha]
    exact pow_dvd_pow 2 hk4
  have hn : orderOf a ≠ 0 := by rw [ha]; exact pow_ne_zero _ (by decide)
  have ho := orderOf_pow_orderOf_div hn hd
  exact no_order_sixteen hlocal hinv (a ^ (orderOf a / 16)) ho

theorem four_two_points_order_four
    (hlocal : SixLocalSylowExponentTwo.EvenSixLocal G X)
    (hinv : ∀ u : G, orderOf u = 2 →
      Nat.card (Function.fixedPoints (toPerm u : Perm X)) ≤ 6)
    (a : G) (k : ℕ) (ha : orderOf a = 2 ^ k)
    (hfour : 0 < Nat.card (FourRoot (toPerm a : Perm X)))
    (htwo : Nat.card (TwoRoot (toPerm a : Perm X)) = 4) :
    orderOf a = 4 ∧ Nat.card (Function.fixedPoints (toPerm a : Perm X)) = 2 := by
  have hk3 := two_power_exponent_le_three hlocal hinv a k ha
  have hd := TwoPartCycleShape.four_dvd_orderOf_of_four_root (toPerm a : Perm X) hfour
  rw [order_toPerm, ha] at hd
  have hk2 : 2 ≤ k := by
    by_contra hn
    have he : k = 0 ∨ k = 1 := by omega
    rcases he with rfl | rfl <;> norm_num at hd
  have hk : k = 2 := by
    have he : k = 2 ∨ k = 3 := by omega
    rcases he with he | rfl
    · exact he
    · have hs := (order_eight_shape hlocal hinv a ha).2.1
      omega
  have hbound := TwoElementFixedBound.fixed_add_two_card_le_six hinv a k hk2 ha
  obtain ⟨E⟩ := TwoRootDoubleSwap.exists_double_two_pattern (toPerm a : Perm X)
    (show 4 ≤ Nat.card (TwoRoot (toPerm a : Perm X)) by omega)
  have hlo := LocalEvenCycleWitness.two_le_fixed_of_double_two hlocal a k ha E
  have hlo' : 2 ≤ Nat.card (Function.fixedPoints (toPerm a : Perm X)) := by
    simpa only [toPermHom_apply] using hlo
  exact ⟨by simpa [hk] using ha, by omega⟩

end FiveTransitive.HigherTwoCycleShape

end CFSG
