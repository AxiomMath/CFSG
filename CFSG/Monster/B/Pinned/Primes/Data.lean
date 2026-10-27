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

namespace CFSG.Monster.B.Pinned

@[expose] def rowsMat (p k : ℕ) (r : List (List ℕ)) : Matrix (Fin k) (Fin k) (ZMod p) :=
  Matrix.of fun i j => ((r.getD i []).getD j 0 : ZMod p)

@[expose] def rowsVec (p k : ℕ) (r : List ℕ) : Fin k → ZMod p := fun i => (r.getD i 0 : ZMod p)

@[expose] def fiveCommRows : List (List ℕ) :=
  [[0, 1, 4, 1], [4, 0, 0, 2], [1, 0, 0, 1], [4, 3, 4, 0]]

@[expose] def fiveActRows : List (List ℕ) :=
  [[0, 0, 1, 0], [0, 0, 0, 1], [2, 2, 4, 2], [1, 4, 4, 0]]

@[expose] def fiveActC : List ℕ := [0, 0, 0, 1]

@[expose] def threeCommRows : List (List ℕ) :=
  [[0, 1, 0, 1, 1, 0, 0, 0], [2, 0, 2, 2, 2, 0, 2, 2], [0, 1, 0, 2, 2, 2, 0, 1],
    [2, 1, 1, 0, 2, 1, 0, 1], [2, 1, 1, 1, 0, 1, 1, 1], [0, 0, 1, 2, 2, 0, 2, 1],
    [0, 1, 0, 0, 2, 1, 0, 1], [0, 1, 2, 2, 2, 2, 2, 0]]

@[expose] def threeXRows : List (List ℕ) :=
  [[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1], [0, 1, 0, 1, 1, 0, 1, 1], [2, 1, 2, 1, 0, 0, 2, 2],
    [1, 2, 0, 2, 2, 1, 0, 1], [1, 1, 1, 0, 2, 1, 1, 1]]

@[expose] def threeYRows : List (List ℕ) :=
  [[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0],
    [2, 1, 2, 1, 0, 2, 2, 1], [1, 1, 1, 1, 1, 2, 1, 2], [1, 0, 2, 1, 1, 0, 2, 2],
    [1, 0, 2, 0, 0, 0, 0, 0], [1, 2, 0, 1, 2, 2, 0, 0]]

@[expose] def threeCVec : List ℕ := [0, 0, 0, 0, 0, 2, 2, 1]

@[expose] def threeDVec : List ℕ := [0, 0, 0, 2, 2, 0, 0, 0]

abbrev MThree : Matrix (Fin 8) (Fin 8) (ZMod 3) := rowsMat 3 8 threeCommRows

abbrev XThree : Matrix (Fin 8) (Fin 8) (ZMod 3) := rowsMat 3 8 threeXRows

abbrev YThree : Matrix (Fin 8) (Fin 8) (ZMod 3) := rowsMat 3 8 threeYRows

abbrev cThree : Fin 8 → ZMod 3 := rowsVec 3 8 threeCVec

abbrev dThree : Fin 8 → ZMod 3 := rowsVec 3 8 threeDVec

abbrev MFive : Matrix (Fin 4) (Fin 4) (ZMod 5) := rowsMat 5 4 fiveCommRows

theorem MFive_eq : MFive = !![0, 1, 4, 1; 4, 0, 0, 2; 1, 0, 0, 1; 4, 3, 4, 0] := by
  decide +kernel

end CFSG.Monster.B.Pinned
