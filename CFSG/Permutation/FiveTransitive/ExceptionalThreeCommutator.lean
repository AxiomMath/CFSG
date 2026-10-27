module

public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG

namespace FiveTransitive.ExceptionalThreeCommutator

open Equiv
open scoped commutatorElement

theorem two_dvd_orderOf_of_exchange
    {X : Type*} [Fintype X] (w : Perm X) {a b : X}
    (hab : a ≠ b) (ha : w a = b) (hb : w b = a) : 2 ∣ orderOf w := by
  have hperiod : Function.IsPeriodicPt w 2 a := by
    change w (w a) = a
    rw [ha, hb]
  have hminimal : Function.minimalPeriod w a = 2 :=
    Function.minimalPeriod_eq_prime hperiod (by change w a ≠ a; rw [ha]; exact hab.symm)
  have hall : Function.IsPeriodicPt w (orderOf w) a := by
    change w^[orderOf w] a = a
    rw [← Perm.coe_pow, pow_orderOf_eq_one]
    rfl
  simpa only [hminimal] using hall.minimalPeriod_dvd

theorem commutator_exchange_first
    {X : Type*} (g v : Perm X) {a b c x : X}
    (ga : g a = b) (_gb : g b = c) (gc : g c = a) (gx : g x = x)
    (vb : v b = b) (va : v a = c) (_vc : v c = x) (vx : v x = a) :
    ⁅g, v⁆ a = b ∧ ⁅g, v⁆ b = a := by
  have v_inv_a : v⁻¹ a = x := v.injective (by simpa only [Perm.inv_def, Equiv.apply_symm_apply] using vx.symm)
  have v_inv_b : v⁻¹ b = b := v.injective (by simpa only [Perm.inv_def, Equiv.apply_symm_apply] using vb.symm)
  have g_inv_x : g⁻¹ x = x := g.injective (by simpa only [Perm.inv_def, Equiv.apply_symm_apply] using gx.symm)
  have g_inv_b : g⁻¹ b = a := g.injective (by simpa only [Perm.inv_def, Equiv.apply_symm_apply] using ga.symm)
  constructor
  · simp only [commutatorElement_def, Perm.mul_apply, v_inv_a, g_inv_x, vx, ga]
  · simp only [commutatorElement_def, Perm.mul_apply, v_inv_b, g_inv_b, va, gc]

theorem commutator_exchange_second
    {X : Type*} (g v : Perm X) {a b c x : X}
    (_ga : g a = b) (gb : g b = c) (gc : g c = a) (gx : g x = x)
    (vb : v b = b) (_va : v a = x) (vx : v x = c) (vc : v c = a) :
    ⁅g, v⁆ a = c ∧ ⁅g, v⁆ c = a := by
  have v_inv_a : v⁻¹ a = c := v.injective (by simpa only [Perm.inv_def, Equiv.apply_symm_apply] using vc.symm)
  have v_inv_c : v⁻¹ c = x := v.injective (by simpa only [Perm.inv_def, Equiv.apply_symm_apply] using vx.symm)
  have g_inv_c : g⁻¹ c = b := g.injective (by simpa only [Perm.inv_def, Equiv.apply_symm_apply] using gb.symm)
  have g_inv_x : g⁻¹ x = x := g.injective (by simpa only [Perm.inv_def, Equiv.apply_symm_apply] using gx.symm)
  constructor
  · simp only [commutatorElement_def, Perm.mul_apply, v_inv_a, g_inv_c, vb, gb]
  · simp only [commutatorElement_def, Perm.mul_apply, v_inv_c, g_inv_x, vx, gc]

theorem support_gt_min_of_even_order
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (m : ℕ)
    (hmin : ∀ g : Perm X, g ∈ P → g ≠ 1 → m ≤ g.support.card)
    (hno : ∀ g : Perm X, g ∈ P → orderOf g = 2 → g.support.card ≠ m)
    {w : Perm X} (hw : w ∈ P) (heven : 2 ∣ orderOf w) :
    m + 1 ≤ w.support.card := by
  let u := w ^ (orderOf w / 2)
  have huorder : orderOf u = 2 :=
    orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos w)) heven
  have huP : u ∈ P := P.pow_mem hw _
  have hune : u ≠ 1 := by
    intro heq
    rw [heq, orderOf_one] at huorder
    omega
  have hle : u.support.card ≤ w.support.card := Finset.card_le_card (Perm.support_pow_le w _)
  have hlow := hmin u huP hune
  have hneq := hno u huP huorder
  omega

end FiveTransitive.ExceptionalThreeCommutator

end CFSG
