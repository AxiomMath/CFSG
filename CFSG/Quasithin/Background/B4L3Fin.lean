module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.L3

open Matrix Matrix.SpecialLinearGroup
open scoped commutatorElement

abbrev Γ := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

abbrev Vec := Fin 3 → ZMod 2

@[expose] def act (g : Γ) (v : Vec) : Vec := (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v

@[expose] def IsInvol (g : Γ) : Prop := g * g = 1 ∧ g ≠ 1

instance : DecidablePred IsInvol := fun g => by unfold IsInvol; infer_instance

@[expose] def cim (g : Γ) : Finset Vec := Finset.univ.image fun v => act g v - v

@[expose] def fixS (g : Γ) : Finset Vec := Finset.univ.filter fun v => act g v = v

@[expose] def cent (z : Γ) : Finset Γ := Finset.univ.filter fun x => x * z = z * x

@[expose] def AS (S : Finset Vec) : Finset Γ := Finset.univ.filter fun g => ∀ v, act g v - v ∈ S

@[expose] def BS (H : Finset Vec) : Finset Γ := Finset.univ.filter fun g => ∀ v ∈ H, act g v = v

theorem act_mul (g h : Γ) (v : Vec) : act (g * h) v = act g (act h v) := by
  unfold act
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]

theorem act_one (v : Vec) : act 1 v = v := by
  unfold act
  simp

theorem act_add (g : Γ) (v w : Vec) : act g (v + w) = act g v + act g w := by
  unfold act
  exact Matrix.mulVec_add _ _ _

theorem act_zero (g : Γ) : act g 0 = 0 := by
  unfold act
  exact Matrix.mulVec_zero _

theorem act_inv_act (g : Γ) (v : Vec) : act g⁻¹ (act g v) = v := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_act_inv (g : Γ) (v : Vec) : act g (act g⁻¹ v) = v := by
  rw [← act_mul, mul_inv_cancel, act_one]

theorem act_sub (g : Γ) (v w : Vec) : act g (v - w) = act g v - act g w := by
  have h := act_add g (v - w) w
  rw [sub_add_cancel] at h
  rw [h]
  abel

theorem act_injective : ∀ g : Γ, (∀ v, act g v = v) → g = 1 := by
  set_option maxRecDepth 100000 in decide +kernel

theorem act_ext {g h : Γ} (hgh : ∀ v, act g v = act h v) : g = h := by
  have : g⁻¹ * h = 1 ∨ True := Or.inr trivial
  have h1 : ∀ v, act (h⁻¹ * g) v = v := by
    intro v
    rw [act_mul, hgh v, act_inv_act]
  have h2 := act_injective _ h1
  calc g = h * (h⁻¹ * g) := by group
    _ = h := by rw [h2, mul_one]

set_option maxRecDepth 100000 in
theorem invol_center : ∀ g : Γ, IsInvol g → ∃ c : Vec, c ≠ 0 ∧ cim g = {0, c} := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem invol_fixS_card : ∀ g : Γ, IsInvol g → (fixS g).card = 4 := by decide +kernel

def t12 : Γ := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩

set_option maxRecDepth 100000 in
theorem conj_to_t12 : ∀ g : Γ, IsInvol g → ∃ x : Γ, x * t12 * x⁻¹ = g := by decide +kernel

theorem conj_invol {g h : Γ} (hg : IsInvol g) (hh : IsInvol h) : ∃ x : Γ, x * g * x⁻¹ = h := by
  obtain ⟨x, hx⟩ := conj_to_t12 g hg
  obtain ⟨y, hy⟩ := conj_to_t12 h hh
  refine ⟨y * x⁻¹, ?_⟩
  rw [← hx] at *
  calc y * x⁻¹ * (x * t12 * x⁻¹) * (y * x⁻¹)⁻¹ = y * t12 * y⁻¹ := by group
    _ = h := hy

set_option maxRecDepth 100000 in
theorem cent_card : ∀ z : Γ, IsInvol z → (cent z).card = 8 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cent_nonabelian :
    ∀ z : Γ, IsInvol z → ∃ x ∈ cent z, ∃ y ∈ cent z, x * y ≠ y * x := by decide +kernel

set_option maxRecDepth 100000 in
theorem cent_two_centers : ∀ z : Γ, IsInvol z →
    ∃ a ∈ cent z, ∃ b ∈ cent z, IsInvol a ∧ IsInvol b ∧ cim a ≠ cim b := by decide +kernel

def x12 : Γ := transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : ZMod 2)

def x23 : Γ := transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : ZMod 2)

def x31 : Γ := transvection (show (2 : Fin 3) ≠ 0 by decide) (1 : ZMod 2)

theorem x12_invol : IsInvol x12 := by unfold IsInvol x12; decide +kernel
theorem x23_invol : IsInvol x23 := by unfold IsInvol x23; decide +kernel
theorem x31_invol : IsInvol x31 := by unfold IsInvol x31; decide +kernel

theorem comm_mem {H : Subgroup Γ} {a b : Γ} (ha : a ∈ H) (hb : b ∈ H) : ⁅a, b⁆ ∈ H :=
  H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem closure_gens : Subgroup.closure ({x12, x23, x31} : Set Γ) = ⊤ := by
  set H := Subgroup.closure ({x12, x23, x31} : Set Γ) with hH
  have h12 : x12 ∈ H := Subgroup.subset_closure (by simp)
  have h23 : x23 ∈ H := Subgroup.subset_closure (by simp)
  have h31 : x31 ∈ H := Subgroup.subset_closure (by simp)
  have h02 : transvection (show (0 : Fin 3) ≠ 2 by decide) (1 : ZMod 2) ∈ H := by
    have := commutatorElement_transvection (show (0 : Fin 3) ≠ 1 by decide)
      (show (1 : Fin 3) ≠ 2 by decide) (show (0 : Fin 3) ≠ 2 by decide) (1 : ZMod 2) (1 : ZMod 2)
    rw [mul_one] at this
    rw [← this]
    exact comm_mem h12 h23
  have h10 : transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : ZMod 2) ∈ H := by
    have := commutatorElement_transvection (show (1 : Fin 3) ≠ 2 by decide)
      (show (2 : Fin 3) ≠ 0 by decide) (show (1 : Fin 3) ≠ 0 by decide) (1 : ZMod 2) (1 : ZMod 2)
    rw [mul_one] at this
    rw [← this]
    exact comm_mem h23 h31
  have h21 : transvection (show (2 : Fin 3) ≠ 1 by decide) (1 : ZMod 2) ∈ H := by
    have := commutatorElement_transvection (show (2 : Fin 3) ≠ 0 by decide)
      (show (0 : Fin 3) ≠ 1 by decide) (show (2 : Fin 3) ≠ 1 by decide) (1 : ZMod 2) (1 : ZMod 2)
    rw [mul_one] at this
    rw [← this]
    exact comm_mem h31 h12
  have hall : ∀ (i j : Fin 3) (hij : i ≠ j) (c : ZMod 2), transvection hij c ∈ H := by
    intro i j hij c
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · rw [transvection_coeff_zero]; exact H.one_mem
    · fin_cases i <;> fin_cases j
      all_goals first | exact absurd rfl hij | assumption
  rw [eq_top_iff,
    ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
      (ι := Fin 3) (K := ZMod 2)]
  rw [Subgroup.closure_le]
  rintro _ ⟨t, rfl⟩
  exact hall t.i t.j t.hij t.c

set_option maxRecDepth 100000 in
theorem act_trans : ∀ c d : Vec, c ≠ 0 → d ≠ 0 → ∃ g : Γ, act g c = d := by decide +kernel

set_option maxRecDepth 100000 in
theorem act_nofix : ∀ v : Vec, v ≠ 0 → ∃ g : Γ, act g v ≠ v := by decide +kernel

set_option maxRecDepth 100000 in
theorem act_allcomm : ∀ w : Vec, ∃ g : Γ, ∃ v : Vec, act g v - v = w := by decide +kernel

set_option maxRecDepth 100000 in
theorem AS_card : ∀ c : Vec, c ≠ 0 → (AS {0, c}).card = 4 := by decide +kernel

set_option maxRecDepth 100000 in
theorem AS_mul : ∀ c : Vec, c ≠ 0 → ∀ g ∈ AS {0, c}, ∀ h ∈ AS {0, c}, g * h ∈ AS {0, c} := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem AS_elem : ∀ c : Vec, c ≠ 0 → ∀ g ∈ AS {0, c}, ∀ h ∈ AS {0, c},
    g * h = h * g ∧ g * g = 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem AS_cim : ∀ c : Vec, c ≠ 0 → ∀ g ∈ AS {0, c}, g ≠ 1 → cim g = {0, c} := by decide +kernel

@[expose] def IsPlane (S : Finset Vec) : Prop :=
  S.card = 4 ∧ 0 ∈ S ∧ ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S

instance : DecidablePred IsPlane := fun S => by unfold IsPlane; infer_instance

set_option maxRecDepth 100000 in
theorem BS_card : ∀ S : Finset Vec, IsPlane S → (BS S).card = 4 := by decide +kernel

set_option maxRecDepth 100000 in
theorem BS_mul : ∀ S : Finset Vec, IsPlane S → ∀ g ∈ BS S, ∀ k ∈ BS S, ∀ v ∈ S,
    act (g * k) v = v := by decide +kernel

set_option maxRecDepth 100000 in
theorem BS_elem : ∀ S : Finset Vec, IsPlane S → ∀ g ∈ BS S, ∀ k ∈ BS S,
    g * k = k * g ∧ g * g = 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem BS_fixS : ∀ S : Finset Vec, IsPlane S → ∀ g ∈ BS S, g ≠ 1 → fixS g = S := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem exists_invol_fixS : ∀ S : Finset Vec, IsPlane S → ∃ g : Γ, IsInvol g ∧ fixS g = S := by
  decide +kernel

end CFSG.Quasithin.L3
