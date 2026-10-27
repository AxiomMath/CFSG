
module

public import Certificates.Data.CFSGNative.Th.Data
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

namespace CFSG.Sporadic.Th.Max3

open CFSG.Sporadic.Th.Native

inductive Gen : Type
  | x : Gen
  | y : Gen
  deriving DecidableEq

@[expose] def Gen.eval {α : Type} (fx fy : α) : Gen → α
  | .x => fx
  | .y => fy

namespace Slp

end Slp

@[expose] def zExp : ℕ := 9

@[expose] def qExp : Fin 8 → ℕ := ![6, 6, 6, 7, 6, 4, 6, 7]

@[expose] def c : Fin 8 → Fin 8 → ZMod 2 :=
  ![![0, 1, 1, 0, 0, 1, 0, 0], ![1, 0, 0, 1, 0, 0, 0, 1], ![1, 0, 0, 0, 1, 0, 1, 1],
    ![0, 1, 0, 0, 1, 1, 1, 0], ![0, 0, 1, 1, 0, 0, 0, 1], ![1, 0, 0, 1, 0, 0, 1, 1],
    ![0, 0, 1, 1, 0, 1, 0, 0], ![0, 1, 1, 0, 1, 1, 0, 0]]

@[expose] def xz : Fin 8 → ZMod 2 := ![0, 0, 1, 1, 0, 1, 0, 1]

@[expose] def xv : Fin 8 → Fin 8 → ZMod 2 :=
  ![![0, 1, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0]]

@[expose] def yz : Fin 8 → ZMod 2 := ![0, 1, 0, 1, 0, 1, 0, 0]

@[expose] def yv : Fin 8 → Fin 8 → ZMod 2 :=
  ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 1, 0, 0, 1], ![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 1, 1, 0, 1, 1], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 1, 0, 0, 1, 0, 1, 0], ![0, 0, 0, 1, 1, 1, 1, 1]]

@[expose] def B1 : Matrix (Fin 8) (Fin 8) (ZMod 2) := Matrix.of fun i j => xv j i

@[expose] def B2 : Matrix (Fin 8) (Fin 8) (ZMod 2) := Matrix.of fun i j => yv j i

@[expose] def B1Cols : Fin 8 → ℕ := ![2, 1, 8, 4, 64, 128, 16, 32]

@[expose] def B2Cols : Fin 8 → ℕ := ![2, 150, 1, 222, 4, 8, 82, 248]

theorem B1_eq_testBit : ∀ j i : Fin 8, B1 i j = if (B1Cols j).testBit i then 1 else 0 := by
  decide

theorem B2_eq_testBit : ∀ j i : Fin 8, B2 i j = if (B2Cols j).testBit i then 1 else 0 := by
  decide

namespace IsRows

end IsRows

@[expose] def powRows (X : Array V4) : ℕ → Array V4
  | 0 => idRows
  | 1 => X
  | n + 2 => mulRows (powRows X (n + 1)) X

@[expose] def prodRows (l : List (Array V4)) : Array V4 := l.foldr mulRows idRows

theorem prodRows_nil : prodRows [] = idRows := List.foldr_nil

@[expose] def wordRows
    (rx ry : Array V4) (w : List Gen) : Array V4 :=
  prodRows (w.map (Gen.eval rx ry))

@[expose] def rowsA : Array V4 := rowsOf seedA

@[expose] def rowsB : Array V4 := rowsOf seedB

namespace Slp

@[expose] def rowsT3 : Array V4 := mulRows rowsA rowsB

@[expose] def rowsT4 : Array V4 := mulRows rowsT3 rowsB

@[expose] def rowsT5 : Array V4 := mulRows rowsT3 rowsT4

@[expose] def rowsT6 : Array V4 := mulRows rowsT3 rowsT5

@[expose] def rowsT7 : Array V4 := mulRows rowsA rowsT6

@[expose] def rowsT8 : Array V4 := mulRows rowsT6 rowsA

@[expose] def rowsU : Array V4 := mulRows (powRows rowsT8 2) rowsT7

@[expose] def rowsS8 : Array V4 := mulRows rowsT6 rowsT5

@[expose] def rowsS9 : Array V4 := mulRows rowsT3 rowsS8

@[expose] def rowsS10 : Array V4 := mulRows rowsS9 rowsT4

@[expose] def rowsS7 : Array V4 := mulRows rowsA rowsS10

@[expose] def rowsS8' : Array V4 := mulRows rowsS10 rowsA

@[expose] def rowsV : Array V4 := mulRows (powRows rowsS8' 18) rowsS7

end Slp

@[expose] def rowsX : Array V4 := powRows Slp.rowsV 14

@[expose] def rowsY : Array V4 := mulRows Slp.rowsT7 (powRows Slp.rowsU 9)

end CFSG.Sporadic.Th.Max3
