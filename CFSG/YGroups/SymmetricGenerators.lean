module

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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

public section

namespace CFSG.YGroups.SymGen

variable {G E Ω : Type*} [Group G] [Group E] [MulAction E Ω]

structure Setup (G E Ω : Type*) [Group G] [Group E] [MulAction E Ω] where
  t : G
  ψ : E →* G
  o : Ω
  w : Ω → E
  t_mul_t : t * t = 1
  w_smul : ∀ p, w p • o = p
  stab_comm : ∀ c : E, c • o = o → ψ c * t = t * ψ c

namespace Setup

variable (S : Setup G E Ω)

@[expose] noncomputable def T (p : Ω) : G := S.ψ (S.w p) * S.t * (S.ψ (S.w p))⁻¹

abbrev H : Subgroup G := S.ψ.range

@[expose] def RCoset (a b : G) : Prop := a * b⁻¹ ∈ S.H

theorem t_inv : S.t⁻¹ = S.t := inv_eq_of_mul_eq_one_right S.t_mul_t

theorem T_eq_of_smul (e : E) (p : Ω) (he : e • S.o = p) :
    S.T p = S.ψ e * S.t * (S.ψ e)⁻¹ := by
  have hc : ((S.w p)⁻¹ * e) • S.o = S.o := by
    rw [mul_smul, he, inv_smul_eq_iff, S.w_smul]
  have hcomm := S.stab_comm _ hc
  rw [map_mul, map_inv] at hcomm
  unfold T
  have : S.ψ e = S.ψ (S.w p) * ((S.ψ (S.w p))⁻¹ * S.ψ e) := by group
  rw [this]
  calc S.ψ (S.w p) * S.t * (S.ψ (S.w p))⁻¹
      = S.ψ (S.w p) * (S.t * ((S.ψ (S.w p))⁻¹ * S.ψ e)) * ((S.ψ (S.w p))⁻¹ * S.ψ e)⁻¹ *
          (S.ψ (S.w p))⁻¹ := by group
    _ = S.ψ (S.w p) * (((S.ψ (S.w p))⁻¹ * S.ψ e) * S.t) * ((S.ψ (S.w p))⁻¹ * S.ψ e)⁻¹ *
          (S.ψ (S.w p))⁻¹ := by rw [hcomm]
    _ = _ := by group

theorem conj_T (e : E) (p : Ω) : S.ψ e * S.T p * (S.ψ e)⁻¹ = S.T (e • p) := by
  rw [S.T_eq_of_smul (e * S.w p) (e • p) (by rw [mul_smul, S.w_smul]), T, map_mul]
  group

theorem mul_T (e : E) (p : Ω) : S.ψ e * S.T p = S.T (e • p) * S.ψ e := by
  rw [← S.conj_T e p]; group

theorem T_mul_self (p : Ω) : S.T p * S.T p = 1 := by
  unfold T
  calc S.ψ (S.w p) * S.t * (S.ψ (S.w p))⁻¹ * (S.ψ (S.w p) * S.t * (S.ψ (S.w p))⁻¹)
      = S.ψ (S.w p) * (S.t * S.t) * (S.ψ (S.w p))⁻¹ := by group
    _ = 1 := by rw [S.t_mul_t]; group

theorem T_inv (p : Ω) : (S.T p)⁻¹ = S.T p := inv_eq_of_mul_eq_one_right (S.T_mul_self p)

theorem T_o : S.T S.o = S.t := by
  rw [S.T_eq_of_smul 1 S.o (one_smul _ _)]; simp

theorem RCoset.refl (a : G) : S.RCoset a a := by
  unfold RCoset; rw [mul_inv_cancel]; exact S.H.one_mem

theorem RCoset.symm {S : Setup G E Ω} {a b : G} (h : S.RCoset a b) : S.RCoset b a := by
  unfold RCoset at *
  have := S.H.inv_mem h
  rwa [mul_inv_rev, inv_inv] at this

theorem RCoset.trans {S : Setup G E Ω} {a b c : G} (h₁ : S.RCoset a b) (h₂ : S.RCoset b c) :
    S.RCoset a c := by
  unfold RCoset at *
  have := S.H.mul_mem h₁ h₂
  rwa [show a * b⁻¹ * (b * c⁻¹) = a * c⁻¹ by group] at this

theorem RCoset.mul_right {S : Setup G E Ω} {a b : G} (h : S.RCoset a b) (g : G) :
    S.RCoset (a * g) (b * g) := by
  unfold RCoset at *
  rwa [show a * g * (b * g)⁻¹ = a * b⁻¹ by group]

theorem RCoset.left_mul {S : Setup G E Ω} {a b : G} (h : S.RCoset a b) (e : E) :
    S.RCoset (S.ψ e * a) (S.ψ e * b) := by
  unfold RCoset at *
  rw [show S.ψ e * a * (S.ψ e * b)⁻¹ = S.ψ e * (a * b⁻¹) * (S.ψ e)⁻¹ by group]
  exact S.H.mul_mem (S.H.mul_mem ⟨e, rfl⟩ h) (S.H.inv_mem ⟨e, rfl⟩)

theorem rcoset_of_conj_mem {x : G} {e : E} (h : x * S.ψ e * x⁻¹ ∈ S.H) (g : G) :
    S.RCoset (x * S.ψ e * g) (x * g) := by
  unfold RCoset
  rw [show x * S.ψ e * g * (x * g)⁻¹ = x * S.ψ e * x⁻¹ by group]
  exact h

theorem act_spec {x y : G} {r₀ p : Ω} {u s h : E} (hent : S.RCoset (x * S.T r₀) (y * S.ψ u))
    (hs : x * S.ψ s * x⁻¹ ∈ S.H) (hsp : s • r₀ = h • p) :
    S.RCoset (x * S.ψ h * S.T p) (y * S.ψ (u * s⁻¹ * h)) := by
  have e1 : x * S.ψ h * S.T p = x * S.ψ s * S.T r₀ * (S.ψ s)⁻¹ * S.ψ h := by
    have := S.conj_T s r₀
    rw [hsp] at this
    calc x * S.ψ h * S.T p = x * (S.ψ h * S.T p * (S.ψ h)⁻¹) * S.ψ h := by group
      _ = x * S.T (h • p) * S.ψ h := by rw [S.conj_T]
      _ = x * (S.ψ s * S.T r₀ * (S.ψ s)⁻¹) * S.ψ h := by rw [this]
      _ = _ := by group
  rw [e1]
  have step1 : S.RCoset (x * S.ψ s * (S.T r₀ * (S.ψ s)⁻¹ * S.ψ h))
      (x * (S.T r₀ * (S.ψ s)⁻¹ * S.ψ h)) := S.rcoset_of_conj_mem hs _
  have step2 := hent.mul_right ((S.ψ s)⁻¹ * S.ψ h)
  have := step1.trans (by
    rw [show x * (S.T r₀ * (S.ψ s)⁻¹ * S.ψ h) = x * S.T r₀ * ((S.ψ s)⁻¹ * S.ψ h) by group]
    exact step2)
  rw [show x * S.ψ s * S.T r₀ * (S.ψ s)⁻¹ * S.ψ h = x * S.ψ s * (S.T r₀ * (S.ψ s)⁻¹ * S.ψ h) by
    group]
  rw [show y * S.ψ (u * s⁻¹ * h) = y * S.ψ u * ((S.ψ s)⁻¹ * S.ψ h) by
    rw [map_mul, map_mul, map_inv]; group]
  exact this

theorem T_mul_T_rel {c : E} (hc2 : S.ψ c * S.ψ c = 1) (hc3 : (S.t * S.ψ c) ^ 3 = 1) (g : E) :
    S.T (g • S.o) * S.T ((g * c) • S.o) = S.ψ (g * c * g⁻¹) * S.T (g • S.o) := by
  have hci : (S.ψ c)⁻¹ = S.ψ c := inv_eq_of_mul_eq_one_right hc2
  have hb : S.t * (S.ψ c * S.t * S.ψ c) = S.ψ c * S.t := by
    have h3 : S.t * S.ψ c * S.t * S.ψ c * S.t * S.ψ c = 1 := by
      rw [pow_three] at hc3; simpa [mul_assoc] using hc3
    calc S.t * (S.ψ c * S.t * S.ψ c) = S.t * S.ψ c * S.t * S.ψ c * S.t * S.ψ c * (S.ψ c)⁻¹ *
          S.t⁻¹ := by group
      _ = (S.ψ c)⁻¹ * S.t⁻¹ := by rw [h3, one_mul]
      _ = S.ψ c * S.t := by rw [hci, S.t_inv]
  have hTc : S.T (c • S.o) = S.ψ c * S.t * S.ψ c := by
    rw [S.T_eq_of_smul c _ rfl, hci]
  have hTo := S.T_o
  have base : S.T S.o * S.T (c • S.o) = S.ψ c * S.T S.o := by
    rw [hTc, hTo, hb]
  have hp : g • S.o = g • S.o := rfl
  have e1 := S.conj_T g S.o
  have e2 := S.conj_T g (c • S.o)
  rw [← mul_smul] at e2
  rw [← e1, ← e2]
  calc S.ψ g * S.T S.o * (S.ψ g)⁻¹ * (S.ψ g * S.T (c • S.o) * (S.ψ g)⁻¹)
      = S.ψ g * (S.T S.o * S.T (c • S.o)) * (S.ψ g)⁻¹ := by group
    _ = S.ψ g * (S.ψ c * S.T S.o) * (S.ψ g)⁻¹ := by rw [base]
    _ = S.ψ (g * c * g⁻¹) * (S.ψ g * S.T S.o * (S.ψ g)⁻¹) := by
        rw [map_mul, map_mul, map_inv]; group

end Setup

end CFSG.YGroups.SymGen
