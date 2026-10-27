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

namespace CFSG.RankThree.Native

inductive FiveIns where
  | mu (i j k : ℕ)
  | pwr (e i k : ℕ)
  deriving Inhabited

@[expose] def fiveSlpStep {M : Type*} [Monoid M] (r : ℕ → M) : FiveIns → ℕ → M
  | .mu i j k => Function.update r k (r i * r j)
  | .pwr e i k => Function.update r k (r i ^ e)

@[expose] def fiveSlpRun {M : Type*} [Monoid M] (prog : List FiveIns) (r : ℕ → M) : ℕ → M :=
  prog.foldl fiveSlpStep r

@[expose] def fiveInit {M : Type*} [Monoid M] (g₁ g₂ : M) (k : ℕ) : M :=
  if k = 1 then g₁ else if k = 2 then g₂ else 1

@[expose] def fiveWord {G : Type*} [Group G] (a b : G) (w : List ℤ) : G :=
  (w.map fun z => if z = 1 then a else if z = 2 then b else if z = -1 then a⁻¹ else b⁻¹).prod

@[expose] def lyFiveProg : List FiveIns := [
  .pwr 1 1 3, .pwr 4 2 4, .pwr 1 1 5, .mu 5 2 5, .mu 5 2 5, .mu 5 1 5, .mu 5 2 5, .mu 5 1 5,
  .mu 5 4 5, .mu 5 4 5, .mu 5 1 5, .mu 5 2 5, .mu 5 2 5, .mu 5 1 5, .mu 5 4 5, .mu 5 1 5,
  .mu 5 2 5, .mu 5 1 5, .mu 5 4 5, .mu 5 4 5, .mu 5 1 5, .mu 5 2 5, .mu 5 2 5, .mu 5 1 5,
  .mu 5 4 5, .mu 5 4 5, .mu 5 1 5, .mu 5 2 5, .mu 5 2 5, .mu 5 1 5, .mu 5 2 5, .mu 5 2 5,
  .pwr 1 1 6, .mu 6 2 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6, .mu 6 2 6,
  .mu 6 2 6, .mu 6 1 6, .mu 6 4 6, .mu 6 1 6, .mu 6 2 6, .mu 6 1 6, .mu 6 4 6, .mu 6 4 6,
  .mu 6 1 6, .mu 6 4 6, .mu 6 4 6, .mu 6 1 6, .mu 6 2 6, .mu 6 2 6, .mu 6 1 6, .mu 6 2 6,
  .mu 6 1 6, .mu 6 4 6, .mu 6 4 6, .mu 6 1 6, .mu 6 4 6, .pwr 14 5 7, .pwr 7 6 8, .pwr 1 5 12,
  .mu 12 7 12, .mu 12 5 12, .mu 12 5 12, .mu 12 5 12, .mu 12 5 12, .mu 12 7 12, .mu 12 6 12,
  .mu 12 8 12, .mu 12 7 12, .mu 12 7 12, .mu 12 5 12, .mu 12 7 12, .mu 12 8 12, .mu 12 6 12,
  .mu 12 7 12, .mu 12 5 12, .mu 12 5 12, .mu 12 8 12, .mu 12 7 12, .mu 12 6 12, .mu 12 5 12,
  .mu 12 7 12, .mu 12 6 12, .pwr 5 12 13, .pwr 1 6 60, .mu 60 5 60, .mu 60 8 60, .mu 60 7 60,
  .mu 60 8 60, .mu 60 5 60, .mu 60 7 60, .mu 60 8 60, .mu 60 5 60, .mu 60 6 60, .mu 60 6 60,
  .mu 60 6 60, .mu 60 7 60, .mu 60 5 60, .mu 60 5 60, .mu 60 7 60, .mu 60 6 60, .mu 60 5 60,
  .mu 60 5 60, .mu 60 7 60, .mu 60 8 60, .mu 60 5 60, .mu 60 6 60, .mu 60 8 60, .pwr 6 60 14,
  .pwr 1 8 60, .mu 60 6 60, .mu 60 6 60, .mu 60 6 60, .mu 60 6 60, .mu 60 8 60, .mu 60 8 60,
  .mu 60 7 60, .mu 60 5 60, .mu 60 6 60, .mu 60 8 60, .mu 60 8 60, .mu 60 7 60, .mu 60 8 60,
  .mu 60 5 60, .mu 60 7 60, .mu 60 8 60, .mu 60 6 60, .mu 60 5 60, .mu 60 5 60, .mu 60 6 60,
  .mu 60 6 60, .mu 60 7 60, .mu 60 5 60, .pwr 4 60 15, .pwr 1 8 60, .mu 60 8 60, .mu 60 5 60,
  .mu 60 8 60, .mu 60 8 60, .mu 60 8 60, .mu 60 6 60, .mu 60 7 60, .mu 60 5 60, .mu 60 8 60,
  .mu 60 5 60, .mu 60 6 60, .mu 60 6 60, .mu 60 5 60, .mu 60 7 60, .mu 60 8 60, .mu 60 5 60,
  .mu 60 6 60, .mu 60 6 60, .mu 60 5 60, .mu 60 5 60, .mu 60 6 60, .mu 60 7 60, .mu 60 8 60,
  .pwr 12 60 16, .pwr 1 8 60, .mu 60 5 60, .mu 60 6 60, .mu 60 7 60, .mu 60 8 60, .mu 60 5 60,
  .mu 60 8 60, .mu 60 6 60, .mu 60 7 60, .mu 60 6 60, .mu 60 7 60, .mu 60 7 60, .mu 60 5 60,
  .mu 60 7 60, .mu 60 6 60, .mu 60 7 60, .mu 60 5 60, .mu 60 6 60, .mu 60 7 60, .mu 60 7 60,
  .mu 60 6 60, .mu 60 7 60, .mu 60 8 60, .mu 60 8 60, .pwr 10 60 17, .pwr 1 6 60, .mu 60 6 60,
  .mu 60 7 60, .mu 60 7 60, .mu 60 5 60, .mu 60 5 60, .mu 60 7 60, .mu 60 6 60, .mu 60 6 60,
  .mu 60 8 60, .mu 60 5 60, .mu 60 7 60, .mu 60 7 60, .mu 60 7 60, .mu 60 5 60, .mu 60 8 60,
  .mu 60 6 60, .mu 60 6 60, .mu 60 5 60, .mu 60 6 60, .mu 60 7 60, .mu 60 7 60, .mu 60 8 60,
  .mu 60 8 60, .pwr 6 60 18, .pwr 1 7 60, .mu 60 8 60, .mu 60 5 60, .mu 60 7 60, .mu 60 5 60,
  .mu 60 8 60, .mu 60 6 60, .mu 60 6 60, .mu 60 8 60, .mu 60 6 60, .mu 60 8 60, .mu 60 7 60,
  .mu 60 5 60, .mu 60 5 60, .mu 60 6 60, .mu 60 7 60, .mu 60 6 60, .mu 60 5 60, .mu 60 7 60,
  .mu 60 8 60, .mu 60 8 60, .mu 60 6 60, .mu 60 6 60, .mu 60 8 60, .pwr 3 60 19, .mu 14 15 20,
  .mu 14 16 21, .mu 14 17 22, .mu 14 18 23, .mu 14 19 24, .pwr 1 8 25, .mu 25 7 25, .mu 25 6 25,
  .mu 25 6 25, .mu 25 8 25, .mu 25 5 25, .mu 25 6 25, .mu 25 7 25, .mu 25 5 25, .mu 25 5 25,
  .mu 25 5 25, .mu 25 5 25, .mu 25 5 25, .mu 25 8 25, .mu 25 6 25, .mu 25 8 25, .mu 25 8 25,
  .mu 25 8 25, .mu 25 7 25, .mu 25 7 25, .mu 25 6 25, .mu 25 6 25, .mu 25 8 25, .mu 25 5 25,
  .pwr 1 5 26, .mu 26 6 26, .mu 26 6 26, .mu 26 7 26, .mu 26 6 26, .mu 26 6 26, .mu 26 6 26,
  .mu 26 6 26, .mu 26 6 26, .mu 26 5 26, .mu 26 7 26, .mu 26 6 26, .mu 26 6 26, .mu 26 5 26,
  .mu 26 8 26, .mu 26 5 26, .mu 26 8 26, .mu 26 7 26, .mu 26 7 26, .mu 26 7 26, .mu 26 5 26,
  .mu 26 6 26, .mu 26 5 26, .mu 26 6 26, .pwr 1 4 61, .mu 61 1 61, .mu 61 2 61, .mu 61 2 61,
  .mu 61 2 61, .mu 61 1 61, .mu 61 2 61, .mu 61 4 61, .mu 61 1 61, .mu 61 1 61, .mu 61 4 61,
  .mu 61 2 61, .mu 61 1 61, .mu 61 4 61, .mu 61 1 61, .mu 61 1 61, .mu 61 2 61, .mu 61 4 61,
  .mu 61 4 61, .mu 61 4 61, .mu 61 1 61, .mu 61 1 61, .mu 61 2 61, .mu 61 1 61, .mu 61 2 61,
  .mu 61 1 61, .mu 61 2 61, .mu 61 4 61, .mu 61 1 61, .mu 61 1 61, .pwr 14 61 62, .mu 62 14 63,
  .mu 63 61 63, .mu 14 63 63, .pwr 9 63 27, .pwr 24 12 28, .pwr 1 14 29, .pwr 1 15 30,
  .pwr 3 25 31, .pwr 19 26 32, .pwr 1 27 33, .pwr 1 31 34, .mu 34 33 34, .mu 34 29 34,
  .mu 34 27 34, .mu 34 28 34, .mu 34 32 34, .mu 34 31 34, .mu 34 26 34, .mu 34 33 34,
  .mu 34 31 34, .pwr 1 12 1, .pwr 1 34 2]

@[expose] def lyFiveVWords : Fin 4 → List ℤ := ![
  [2, -1, -2, -1, -2, 1, 2, -1, -2, -1, -2, 1, 2, -1, -2, -1, -2, 1, 2, -1, -2, -1, -2, 1],
  [-2, -2, -1, -2, -1, -2, -2, -2, -1, -2, -1, -2, -2, -2, -1, -2, -1, -2],
  [2, -1, -2, 1, -2, -1, 2, -1, -2, 1, -2, -1, 2, -1, -2, 1, -2, -1, 2, -1, -2, 1, -2, -1],
  [2, -1, 2, 1, 2, 1, 2, -1, 2, 1, 2, 1, 2, -1, 2, 1, 2, 1, 2, -1, 2, 1, 2, 1]]

@[expose] def fiveDigits (q : ℕ) : ZMod 5 × (Fin 4 → ZMod 5) :=
  (((q % 5 : ℕ) : ZMod 5), fun i => (((q / 5 ^ (i.val + 1)) % 5 : ℕ) : ZMod 5))

end CFSG.RankThree.Native

namespace CFSG.RankThree.PartOne.LyFive

@[expose] def xWord : List ℤ := [2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2]

@[expose] def y3Word : List ℤ := [1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2]

@[expose] def y1Word : List ℤ := [2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1]

end CFSG.RankThree.PartOne.LyFive
