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

namespace CFSG.Quasithin

@[expose] def g2Letter (c : Char) : ℕ × ℤ :=
  if c = 'a' then (0, 1) else if c = 'b' then (1, 1) else if c = 'c' then (2, 1) else (5, 1)

@[expose] def g2W (s : String) : List (ℕ × ℤ) := s.toList.map g2Letter

@[expose] def g2Inv (w : List (ℕ × ℤ)) : List (ℕ × ℤ) := w.reverse.map fun f => (f.1, -f.2)

@[expose] def g2GenWord (i : ℕ) : List (ℕ × ℤ) :=
  g2W (["bcabacdb", "abcabacdba", "a", "dcad", "bd"].getD i "")

@[expose] def g2PL (l : Fin 5 × Bool) : List (ℕ × ℤ) :=
  if l.2 then g2GenWord l.1 else g2Inv (g2GenWord l.1)

@[expose] def g2PW (w : List (Fin 5 × Bool)) : List (ℕ × ℤ) := w.flatMap g2PL

@[expose] def g2Comm (g h : List (ℕ × ℤ)) : List (ℕ × ℤ) := g ++ h ++ g2Inv g ++ g2Inv h

@[expose] def g2LetterStr (t : ℕ) : String := ["a", "b", "c", "d"].getD t ""

@[expose] def g2CommG : List String := ["cd", "cd", "d", "a", "b"]

@[expose] def g2CommH : List String := ["babdcbaba", "dbabacb", "cabac", "dc", "bd"]

@[expose] def g2ConjStrings : List String :=
  ["b", "a", "s", "X", "aYA", "YAy", "sya", "aa", "Ayxy", "Y", "BYxYXY", "AsYXYXY", "AYxaY", "xyBxyXy", "AYXYBXY", "bys", "asy", "s", "yaxAY", "Y"]

@[expose] def g2CommStrings : List String :=
  ["", "bbs", "yaxAY", "", "aas", "", "", "Y", "aYAXY", "", "", "yaxAYX", "", "y", "AxYbXY", ""]

@[expose] def g2CPres : String := "ysXY"

end CFSG.Quasithin
