module

public import CFSG.Sporadic.Fi23.InvCertInputs
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

@[expose] public section

namespace CFSG.Sporadic.Fi23.Native

open CFSG.Sporadic.Th.Native CFSG.Perm.Native

set_option compiler.extract_closed false

@[expose] def s12Pts : Array Nat :=
  #[0, 4953, 15723, 20053, 6049, 8308, 8379, 145, 17454, 5528, 14172]

@[expose] def s12Tab (O : WOrbit) (i : Nat) : Table :=
  treeActTab O (dTab O) (genTables O (-2)) s12Pts[i]!

@[expose] def s12Braid (O : WOrbit) (i : Nat) : Bool :=
  compT 31671 (compT 31671 (s12Tab O i) (s12Tab O (i + 1))) (s12Tab O i) ==
    compT 31671 (compT 31671 (s12Tab O (i + 1)) (s12Tab O i)) (s12Tab O (i + 1))

@[expose] def s12Comm (O : WOrbit) (i j : Nat) : Bool :=
  compT 31671 (s12Tab O i) (s12Tab O j) == compT 31671 (s12Tab O j) (s12Tab O i)

@[expose] def s12P4 (O : WOrbit) : Table :=
  compT 31671 (compT 31671 (compT 31671 (s12Tab O 0) (s12Tab O 2)) (s12Tab O 4)) (s12Tab O 6)

@[expose] def s12P6 (O : WOrbit) : Table :=
  compT 31671 (compT 31671 (s12P4 O) (s12Tab O 8)) (s12Tab O 10)

@[expose] def s12Checks (O : WOrbit) : Bool :=
  allIn 0 11 (fun i => decide (s12Pts[i]! < 31671)) &&
    allIn 0 10 (fun i => s12Braid O i) &&
    allIn 0 11 (fun i => allIn 0 11 (fun j => decide (j < i + 2) || s12Comm O i j)) &&
    invoOK 31671 (s12P4 O) && !isIdT (s12P4 O) && fixCount (s12P4 O) == 183 &&
    invoOK 31671 (s12P6 O) && !isIdT (s12P6 O) && fixCount (s12P6 O) == 695

@[expose] def s12Certificate : Bool := s12Checks (orbitData ())

end CFSG.Sporadic.Fi23.Native
