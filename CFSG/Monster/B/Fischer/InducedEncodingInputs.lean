module

public import CFSG.Monster.B.Fischer.ArrCert
public import CFSG.Monster.B.Classical.Derived22Data
public import CFSG.Monster.B.TwoA.Census.PermCert
public import CFSG.Sporadic.Mathieu.Actions
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
public import Mathlib.GroupTheory.Nilpotent
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

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.Code CFSG.Monster.B.Classical.Mog22 CFSG.Monster.B.TwoA CFSG.Sporadic.Mathieu

@[expose] def aCat : Array ℕ :=
  #[12, 7, 15, 11, 4, 21, 16, 1, 9, 8, 13, 3, 0, 10, 14, 2, 6, 17, 18, 19, 20, 5]

@[expose] def bCat : Array ℕ :=
  #[21, 17, 20, 12, 11, 10, 14, 13, 8, 7, 6, 4, 1, 19, 5, 15, 18, 3, 16, 9, 0, 2]

@[expose] def bInvCat : Array ℕ :=
  #[20, 12, 21, 17, 11, 14, 10, 9, 8, 19, 5, 4, 3, 7, 6, 15, 18, 1, 16, 13, 2, 0]

@[expose] def letterCat (z : ℤ) : Array ℕ :=
  if z = 1 then aCat else if z = -1 then aCat else if z = 2 then bCat else bInvCat

@[expose] def wordCat (w : List ℤ) : Array ℕ :=
  w.foldr (fun z acc => amulN (letterCat z) acc) (idArrN 22)

@[expose] def blockWord (i : ℕ) : List ℤ :=
  [[], [1, 2, 2], [1, 2, 1], [1], [2, 1, 2, 1, 2, 2, 1, 2], [2, 1, 2, 2, 2, 1, 2, 1, 2, 1],
    [1, 2, 1, 2, 2, 1, 2, 1], [1, 2, 2, 1, 2, 2, 1, 2], [2, 2, 1, 2],
    [2, 2, 1, 2, 1, 2, 2, 1, 2, 1], [2], [2, 1, 2, 1, 2, 2, 2, 1, 2], [2, 2, 2, 1, 2, 2, 2, 1, 2],
    [1, 2, 2, 1, 2, 1], [2, 2, 1, 2, 2], [2, 2, 1, 2, 1, 2, 2, 2], [2, 2, 1, 2, 2, 2],
    [2, 2, 2, 1, 2, 1, 2, 2, 1, 2], [1, 2, 2, 2, 1, 2, 2, 2], [2, 2, 1, 2, 1, 2, 2, 2, 1, 2],
    [1, 2, 1, 2, 1, 2, 1], [1, 2, 2, 2, 1, 2, 1, 2, 1], [2, 1, 2, 1, 2, 2, 2], [2, 1, 2, 1, 2, 1],
    [2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1], [2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1],
    [1, 2, 1, 2, 2, 1, 2, 2, 1, 2], [2, 2, 2, 1, 2, 1, 2, 2], [2, 1, 2], [2, 1, 2, 1, 2],
    [2, 2, 1, 2, 1, 2, 2], [2, 1, 2, 2], [1, 2, 1, 2, 1], [1, 2, 2, 2, 1, 2, 2], [2, 2, 2, 1, 2],
    [1, 2, 2, 2, 1, 2], [1, 2, 2, 1, 2, 1, 2, 2, 1, 2], [2, 1, 2, 2, 1, 2],
    [2, 2, 1, 2, 1, 2, 2, 1, 2], [2, 2, 2, 1, 2, 2, 1, 2], [1, 2, 2, 1, 2],
    [1, 2, 1, 2, 2, 2, 1, 2], [2, 1, 2, 2, 2, 1, 2, 2, 2], [2, 1, 2, 2, 1, 2, 1], [1, 2],
    [1, 2, 2, 2], [1, 2, 2, 1, 2, 2, 2], [2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2],
    [2, 2, 2, 1, 2, 1, 2, 1], [2, 1, 2, 2, 1, 2, 2, 2], [2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2],
    [1, 2, 2, 2, 1, 2, 1, 2, 2], [1, 2, 1, 2, 2], [2, 2, 2, 1, 2, 1], [2, 2, 2, 1, 2, 2],
    [1, 2, 2, 1, 2, 1, 2, 1], [2, 1], [2, 2], [2, 2, 1, 2, 2, 1, 2], [2, 1, 2, 2, 2],
    [1, 2, 1, 2, 1, 2, 2, 2, 1, 2], [2, 2, 2], [2, 2, 1, 2, 1], [2, 2, 1, 2, 2, 1, 2, 1],
    [1, 2, 1, 2, 1, 2, 2, 2], [2, 1, 2, 1, 2, 2, 1, 2, 1], [2, 1, 2, 1, 2, 2],
    [2, 1, 2, 2, 1, 2, 2, 1, 2], [1, 2, 1, 2], [2, 2, 1, 2, 2, 2, 1, 2], [2, 1, 2, 1],
    [2, 2, 1, 2, 1, 2, 1], [1, 2, 1, 2, 2, 2], [2, 1, 2, 2, 2, 1, 2], [2, 2, 2, 1, 2, 2, 1, 2, 1],
    [2, 2, 2, 1, 2, 2, 2], [1, 2, 1, 2, 2, 1, 2]].getD i []

@[expose] def hCat (i : ℕ) : Array ℕ := wordCat (blockWord i)

@[expose] def catB₀ : Finset (Fin 22) := {0, 1, 2, 9, 17, 19}

@[expose] def hexCat (arr : Array ℕ) : Finset (Fin 22) := catB₀.image (arrFunN 22 arr)

end CFSG.Monster.B.Fischer
