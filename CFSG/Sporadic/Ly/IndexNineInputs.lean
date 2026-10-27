module

public import CFSG.Sporadic.SmallOddCore.GroupFacts
public import Certificates.Data.CFSGNative.Th.Core
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
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

namespace CFSG.Sporadic.Ly

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native

attribute [local instance] Finset.smulFinset Finset.mulActionFinset

@[expose] def lyA : Finset (Fin 11) := {0, 1, 2, 3}

@[expose] def lyB : Finset (Fin 11) := {4, 5, 6, 7}

@[expose] def lyBlockC : Finset (Fin 11) := {8, 9}

@[expose] def lyD : Finset (Fin 11) := {10}

@[expose] def lyX0 : Finset (Finset (Fin 11)) := {lyA, lyB, lyBlockC, lyD}

@[expose] def lyO8 : Finset (Fin 11) := lyA ∪ lyB

@[expose] def lyUG1 : Equiv.Perm (Fin 11) :=
  Equiv.swap 0 4 * Equiv.swap 1 5 * Equiv.swap 2 6 * Equiv.swap 3 7

@[expose] def lyUG2 : Equiv.Perm (Fin 11) := Equiv.swap 6 7 * Equiv.swap 8 9

@[expose] def lyUG3 : Equiv.Perm (Fin 11) := Equiv.swap 4 6 * Equiv.swap 5 7

@[expose] def lyUGensPerm : List (Equiv.Perm (Fin 11)) := [lyUG1, lyUG2, lyUG3]

@[expose] def lyXPerm : Equiv.Perm (Fin 11) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def lyYPerm : Equiv.Perm (Fin 11) := Equiv.swap 4 5 * Equiv.swap 5 6

@[expose] def lyUInvariantCheck (size : Nat) (target : Finset (Fin 11))
    (_ : Unit := ()) : Bool :=
  (((Finset.univ : Finset (Fin 11)).powerset.filter fun s =>
      s.card = size ∧ (lyUGensPerm.all fun g => decide (g • s = s)) = true).erase target).card
    == 0

@[expose] def lySplitStable (s : Finset (Fin 11)) : Bool :=
  lyUGensPerm.all fun g => decide (g • s = s) || decide (g • s = lyO8 \ s)

@[expose] def lySplitCheck (_ : Unit := ()) : Bool :=
  ((lyO8.powerset.filter fun s =>
      s.card = 4 ∧ (0 : Fin 11) ∈ s ∧ lySplitStable s = true).erase lyA).card == 0

end CFSG.Sporadic.Ly
