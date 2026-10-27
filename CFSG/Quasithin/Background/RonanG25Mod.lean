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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.RonanG25

section Mod

variable {Γ : Type} [Group Γ] {F : Type} [Field F] {E : Type} [AddCommGroup E]

@[expose] def AInv (act : Γ → E →+ E) (M : AddSubgroup E) : Prop :=
  ∀ x : Γ, ∀ e ∈ M, act x e ∈ M

structure ModStep (act : Γ → E →+ E) (M₁ M₂ : AddSubgroup E) : Prop where
  lt : M₁ < M₂
  inv₁ : AInv act M₁
  inv₂ : AInv act M₂
  simple : ∀ M : AddSubgroup E, M₁ ≤ M → M ≤ M₂ → AInv act M → M = M₁ ∨ M = M₂

@[expose] def ModNatural (F : Type) [Field F] (act : Γ → E →+ E) (M₁ M₂ : AddSubgroup E) : Prop :=
  ∃ (c : E →+ (Fin 2 → F)) (β : Γ →* Matrix.GeneralLinearGroup (Fin 2) F),
    (∀ w : Fin 2 → F, ∃ e ∈ M₂, c e = w) ∧ (∀ e ∈ M₂, c e = 0 ↔ e ∈ M₁) ∧
    (∀ x : Γ, ∀ e ∈ M₂, c (act x e) =
      ((β x : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec (c e)) ∧
    (Nat.card F = 2 → β ≠ 1) ∧
    (2 < Nat.card F → ∀ M : Matrix.SpecialLinearGroup (Fin 2) F, ∃ x : Γ,
      ((β x : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (M : Matrix (Fin 2) (Fin 2) F))

@[expose] def ModAdditional (F : Type) [Field F] (act : Γ → E →+ E) (M₁ M₂ : AddSubgroup E) :
    Prop :=
  Nat.card M₂ = Nat.card F * Nat.card M₁ ∧ ∃ x : Γ, ∃ e ∈ M₂, act x e - e ∉ M₁

@[expose] def ModCentral (act : Γ → E →+ E) (M₁ M₂ : AddSubgroup E) : Prop :=
  (∀ x : Γ, ∀ e ∈ M₂, act x e - e ∈ M₁) ∧ ∃ p : ℕ, p.Prime ∧ Nat.card M₂ = p * Nat.card M₁

inductive ModChain (F : Type) [Field F] (act : Γ → E →+ E) :
    AddSubgroup E → AddSubgroup E → ℕ → ℕ → Prop
  | refl (M : AddSubgroup E) (hM : AInv act M) : ModChain F act M M 0 0
  | natural {M₁ M₂ M₃ : AddSubgroup E} {a b : ℕ} (hs : ModStep act M₁ M₂)
      (hn : ModNatural F act M₁ M₂) (rest : ModChain F act M₂ M₃ a b) :
      ModChain F act M₁ M₃ (a + 1) b
  | additional {M₁ M₂ M₃ : AddSubgroup E} {a b : ℕ} (hs : ModStep act M₁ M₂)
      (hn : ModAdditional F act M₁ M₂) (rest : ModChain F act M₂ M₃ a b) :
      ModChain F act M₁ M₃ a (b + 1)
  | central {M₁ M₂ M₃ : AddSubgroup E} {a b : ℕ} (hs : ModStep act M₁ M₂)
      (hn : ModCentral act M₁ M₂) (rest : ModChain F act M₂ M₃ a b) :
      ModChain F act M₁ M₃ a b

theorem ModChain.trans {act : Γ → E →+ E} {M₁ M₂ M₃ : AddSubgroup E} {a b a' b' : ℕ}
    (h : ModChain F act M₁ M₂ a b) (h' : ModChain F act M₂ M₃ a' b') :
    ModChain F act M₁ M₃ (a + a') (b + b') := by
  induction h with
  | refl M hM => simpa using h'
  | natural hs hn rest ih =>
    have := ModChain.natural hs hn (ih h')
    simpa [Nat.add_right_comm] using this
  | additional hs hn rest ih =>
    have := ModChain.additional hs hn (ih h')
    simpa [Nat.add_right_comm] using this
  | central hs hn rest ih => exact ModChain.central hs hn (ih h')

theorem ModChain.le {act : Γ → E →+ E} {M₁ M₂ : AddSubgroup E} {a b : ℕ}
    (h : ModChain F act M₁ M₂ a b) : M₁ ≤ M₂ := by
  induction h with
  | refl M hM => exact le_rfl
  | natural hs hn rest ih => exact hs.lt.le.trans ih
  | additional hs hn rest ih => exact hs.lt.le.trans ih
  | central hs hn rest ih => exact hs.lt.le.trans ih

end Mod

end CFSG.Quasithin.RonanG25
