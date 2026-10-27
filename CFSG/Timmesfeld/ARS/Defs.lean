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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Timmesfeld.ARS

variable {G : Type*} [Group G]

abbrev conjSub (A : Subgroup G) (g : G) : Subgroup G := A.map (MulAut.conj g).toMonoidHom

@[expose] def Commuting (A B : Subgroup G) : Prop := ∀ a ∈ A, ∀ b ∈ B, Commute a b

@[expose] def Opposite (A B : Subgroup G) : Prop :=
  A ≠ B ∧
  (∀ a ∈ A, a ≠ 1 → ∃ b ∈ B, b ≠ 1 ∧ conjSub A b = conjSub B a) ∧
  (∀ b ∈ B, b ≠ 1 → ∃ a ∈ A, a ≠ 1 ∧ conjSub B a = conjSub A b)

@[expose] def Special (R : Set (Subgroup G)) (A B : Subgroup G) : Prop :=
  ⁅A, B⁆ ∈ R ∧ Commuting ⁅A, B⁆ A ∧ Commuting ⁅A, B⁆ B

structure IsRootClass (R : Set (Subgroup G)) : Prop where
  conj_class : ∃ A₀ : Subgroup G, R = Set.range (conjSub A₀)
  ne_bot : ∀ A ∈ R, A ≠ ⊥
  mul_self : ∀ A ∈ R, ∀ a ∈ A, a * a = 1
  rel : ∀ A ∈ R, ∀ B ∈ R, A ≠ B → Commuting A B ∨ Opposite A B ∨ Special R A B
  gen : ⨆ A ∈ R, A = ⊤

@[expose] def IsNondegenerate (R : Set (Subgroup G)) : Prop := ∃ A ∈ R, ∃ B ∈ R, Special R A B

@[expose] def CoveredBy (R : Set (Subgroup G)) (H : Subgroup G) : Prop :=
  ∀ x ∈ H, x ≠ 1 → ∃ C ∈ R, C ≤ H ∧ x ∈ C

@[expose] def centralSet (R : Set (Subgroup G)) (A : Subgroup G) : Set (Subgroup G) :=
  {B | B ∈ R ∧ Commuting A B}

@[expose] def sigmaSet (R : Set (Subgroup G)) (A : Subgroup G) : Set (Subgroup G) :=
  {B | B ∈ R ∧ B ≠ A ∧ Commuting A B}

@[expose] def lambdaSet (R : Set (Subgroup G)) (A : Subgroup G) : Set (Subgroup G) :=
  {B | B ∈ sigmaSet R A ∧ CoveredBy R (A ⊔ B)}

@[expose] def psiSet (R : Set (Subgroup G)) (A : Subgroup G) : Set (Subgroup G) :=
  {B | B ∈ R ∧ Special R A B}

@[expose] def omegaSet (R : Set (Subgroup G)) (A : Subgroup G) : Set (Subgroup G) :=
  {B | B ∈ R ∧ Opposite A B}

@[expose] def M (R : Set (Subgroup G)) (A : Subgroup G) : Subgroup G :=
  A ⊔ ⨆ B ∈ lambdaSet R A, B

@[expose] def isolatedSet (R : Set (Subgroup G)) (D : Subgroup G) : Set (Subgroup G) :=
  {B | B ∈ centralSet R D ∧ ∀ C ∈ centralSet R D, ¬ Opposite B C}

@[expose] def Q (R : Set (Subgroup G)) (D : Subgroup G) : Subgroup G :=
  ⨆ B ∈ isolatedSet R D, B

@[expose] def rootClosure (R : Set (Subgroup G)) (A : Subgroup G) : Set (Subgroup G) :=
  {B | B ∈ R ∧ centralSet R B = centralSet R A}

@[expose] def rootElts (R : Set (Subgroup G)) : Set G := {a | ∃ A ∈ R, a ∈ A ∧ a ≠ 1}

@[expose] def leviSet (R : Set (Subgroup G)) (A A₀ : Subgroup G) : Set (Subgroup G) :=
  sigmaSet R A ∩ sigmaSet R A₀

@[expose] def levi (R : Set (Subgroup G)) (A A₀ : Subgroup G) : Subgroup G :=
  ⨆ B ∈ leviSet R A A₀, B

@[expose] def lambdaStar (R : Set (Subgroup G)) (A A₀ : Subgroup G) : Set (Subgroup G) :=
  lambdaSet R A ∩ psiSet R A₀

@[expose] def NoIsolated (R : Set (Subgroup G)) : Prop := ∀ A ∈ R, ∃ B ∈ R, Opposite A B

structure Hyp (G : Type*) [Group G] (R : Set (Subgroup G)) : Prop where
  finite : Finite G
  root : IsRootClass R
  nondeg : IsNondegenerate R
  center : Subgroup.center G = ⊥
  twoCore : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥

end CFSG.Timmesfeld.ARS
