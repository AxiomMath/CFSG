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
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
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

namespace CFSG.Open

@[expose] def monsterY443ArmLength : Fin 3 → ℕ
  | 0 => 4
  | 1 => 4
  | 2 => 3

abbrev MonsterY443Gen : Type := Option (Σ i : Fin 3, Fin (monsterY443ArmLength i))

@[expose] def MonsterY443Adj : MonsterY443Gen → MonsterY443Gen → Prop
  | none, none => False
  | none, some ⟨_, j⟩ => j.val = 0
  | some ⟨_, j⟩, none => j.val = 0
  | some ⟨i, j⟩, some ⟨i', j'⟩ => i = i' ∧ (j.val + 1 = j'.val ∨ j'.val + 1 = j.val)

@[expose] def monsterY443Node (i : Fin 3) (j : ℕ) (hj : j < monsterY443ArmLength i) :
    FreeGroup MonsterY443Gen :=
  FreeGroup.of (some ⟨i, ⟨j, hj⟩⟩)

@[expose] def monsterY443SpiderWord : FreeGroup MonsterY443Gen :=
  FreeGroup.of none * monsterY443Node 0 0 (by decide) * monsterY443Node 0 1 (by decide) *
    FreeGroup.of none * monsterY443Node 1 0 (by decide) * monsterY443Node 1 1 (by decide) *
    FreeGroup.of none * monsterY443Node 2 0 (by decide) * monsterY443Node 2 1 (by decide)

@[expose] def monsterY443Rels : Set (FreeGroup MonsterY443Gen) :=
  {w | ∃ s, w = FreeGroup.of s ^ 2} ∪
  {w | ∃ s t, MonsterY443Adj s t ∧ w = (FreeGroup.of s * FreeGroup.of t) ^ 3} ∪
  {w | ∃ s t, s ≠ t ∧ ¬ MonsterY443Adj s t ∧ w = (FreeGroup.of s * FreeGroup.of t) ^ 2} ∪
  {monsterY443SpiderWord ^ 10}

abbrev MonsterY443 : Type := PresentedGroup monsterY443Rels

abbrev MonsterY443Derived : Subgroup MonsterY443 := commutator MonsterY443

end CFSG.Open
