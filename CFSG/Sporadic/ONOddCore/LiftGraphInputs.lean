module

public import CFSG.Sporadic.HNOddCore.ChainUtil
public import CFSG.Sporadic.ONOddCore.GraphDefs
public import CFSG.Sporadic.ONOddCore.LiftPayload
public import Certificates.Data.CFSGNative.ON.Certificate
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

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native

@[expose] def liftResText : String := include_str "Data"/"liftres.txt"

@[expose] def liftResNats : List Nat := natsOf liftResText

@[expose] def resY : Array Nat := (liftResNats.take 480).toArray

@[expose] def resArr (j : Nat) : Array Nat := ((liftResNats.drop (480 * (j + 1))).take 480).toArray

@[expose] def resArrs : Array (Array Nat) := #[resArr 0, resArr 1, resArr 2]

@[expose] def resW : Array (List Int) :=
  #[[], [], [], [3, 2, 2, -3, -3, -3], [2, -3, 4, -3], [4, 4, -5, -4], [-5, -6, 5, 4, 4],
    [-2, 3, -2, 4, 2]]

@[expose] def resBase : List (Fin 480) := [0, 1, 2]

@[expose] def resBase2 : List (Fin 960) := [0, 1, 2]

@[expose] def resSizes : List Nat := [480, 42, 8]

@[expose] def resLift (e : LiftEntry) : Array (Array Nat) :=
  (e.words.map (posArr 480 resArrs)).toArray

@[expose] def resPair (e : LiftEntry) : Array (Array Nat) :=
  #[dbl 480 resArrs[0]! (resLift e)[0]!, dbl 480 resArrs[1]! (resLift e)[1]!,
    dbl 480 resArrs[2]! (resLift e)[2]!]

@[expose] def resQ : Array Nat := posArr 480 resArrs liftData.qWord

@[expose] def resQPow : Nat → Array Nat
  | 0 => pid 480
  | k + 1 => pcomp 480 resQ (resQPow k)

@[noinline, expose] def liftResOK (hA : Array (Array Nat)) : Bool :=
  resY.size == 480 && allBelowN 479 (fun k => decide (resY[k]! < resY[k + 1]!)) &&
    decide (resY[479]! < nPts) &&
    allBelowN 3 (fun j => (resArrs[j]!).size == 480 && allBelowN 480 fun k =>
      decide ((resArrs[j]!)[k]! < 480) && resY[(resArrs[j]!)[k]!]! == (hA[j]!)[resY[k]!]!) &&
    CFSG.Sporadic.HNOddCore.chainCheck 480 resArrs resW resBase resSizes

@[noinline, expose] def liftGraphOK (e : LiftEntry) : Bool :=
  CFSG.Sporadic.HNOddCore.chainCheck 960 (resPair e) resW resBase2 resSizes &&
    peq 480 (posArr 480 (resLift e) liftData.qWord) (resQPow e.power)

end CFSG.Sporadic.ONOddCore
