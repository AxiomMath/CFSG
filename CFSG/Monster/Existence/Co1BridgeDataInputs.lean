module

public import CFSG.Monster.VisCert.Basis
public import Certificates.Data.CFSGNative.HS.SmallF2
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

namespace CFSG.Monster.Existence.Co1Bridge

open CFSG.Monster.VisCert CFSG.Sporadic.SmallF2.Native

@[expose] def xWord : List ℕ :=
  [1, 10, 4, 13, 1, 4, 0, 13, 12, 9, 11, 5, 12, 2, 7, 13, 6, 2, 3, 0, 0, 3, 12, 1, 12, 9, 14, 0,
  14, 7, 3, 4, 0, 4, 9, 2, 8, 9, 1, 10, 4, 13, 1, 4, 0, 13, 12, 9, 11, 5, 12, 2, 7, 13, 6, 2, 3,
  0, 0, 3, 12, 1, 12, 9, 14, 0, 14, 7, 3, 4, 0, 4, 9, 2, 8, 9, 1, 10, 4, 13, 1, 4, 0, 13, 12, 9,
  11, 5, 12, 2, 7, 13, 6, 2, 3, 0, 0, 3, 12, 1, 12, 9, 14, 0, 14, 7, 3, 4, 0, 4, 9, 2, 8, 9, 1,
  10, 4, 13, 1, 4, 0, 13, 12, 9, 11, 5, 12, 2, 7, 13, 6, 2, 3, 0, 0, 3, 12, 1, 12, 9, 14, 0, 14,
  7, 3, 4, 0, 4, 9, 2, 8, 9, 1, 10, 4, 13, 1, 4, 0, 13, 12, 9, 11, 5, 12, 2, 7, 13, 6, 2, 3, 0, 0,
  3, 12, 1, 12, 9, 14, 0, 14, 7, 3, 4, 0, 4, 9, 2, 8, 9, 1, 10, 4, 13, 1, 4, 0, 13, 12, 9, 11, 5,
  12, 2, 7, 13, 6, 2, 3, 0, 0, 3, 12, 1, 12, 9, 14, 0, 14, 7, 3, 4, 0, 4, 9, 2, 8, 9]

@[expose] def yWord : List ℕ :=
  [12, 8, 12, 10, 6, 2, 2, 9, 10, 1, 0, 0, 2, 2, 10, 2, 2, 5, 2, 2, 5, 10, 1, 10, 1, 3, 9, 2, 2,
  10, 5, 4, 5, 7, 14, 5, 8, 2, 6, 0, 1, 6, 4, 8, 2, 6, 12, 4, 13, 1, 14, 6, 0, 0, 6, 2, 8, 3, 12,
  3, 1, 4, 5, 7, 14, 5, 8, 2, 6, 0, 1, 6, 4, 8, 2, 6, 12, 4, 13, 1, 14, 6, 0, 0, 6, 2, 8, 3, 12,
  3, 1, 4, 5, 7, 14, 5, 8, 2, 6, 0, 1, 6, 4, 8, 2, 6, 12, 4, 13, 1, 14, 6, 0, 0, 6, 2, 8, 3, 12,
  3, 1, 4, 5, 7, 14, 5, 8, 2, 6, 0, 1, 6, 4, 8, 2, 6, 12, 4, 13, 1, 14, 6, 0, 0, 6, 2, 8, 3, 12,
  3, 1, 4, 5, 7, 14, 5, 8, 2, 6, 0, 1, 6, 4, 8, 2, 6, 12, 4, 13, 1, 14, 6, 0, 0, 6, 2, 8, 3, 12,
  3, 1, 5, 10, 2, 9, 3, 1, 10, 1, 10, 5, 2, 5, 2, 10, 2, 0, 1, 10, 9, 2, 6, 10, 12, 8, 12]

@[expose] def eRows : Array ℕ :=
  #[2672, 8591866, 9314279, 4811400, 12122727, 5311623, 12785402, 16574555, 8323190, 10220987,
  7668657, 12548723, 4780434, 11645774, 12054002, 7258922, 6937565, 15522814, 13826211, 14524552,
  16282692, 14389455, 1948705, 14172184]

@[expose] def eInvRows : Array ℕ :=
  #[13425076, 9016948, 13913813, 12198523, 15969749, 9490629, 76215, 75196, 4266678, 6404305,
  2253968, 257143, 5468808, 8160368, 8964326, 8685025, 3453099, 11087855, 4125109, 1607062,
  8664583, 96932, 76482, 14474779]

@[expose] def atRows : Array ℕ :=
  #[2293352, 14979871, 1051873, 7463284, 3113190, 15858749, 8255772, 8056098, 3550559, 2546458,
  4683979, 4207809, 12725466, 8657426, 5006561, 16229128, 11250310, 13084505, 11688799, 13477721,
  13851237, 15082812, 2403413, 14527399]

@[expose] def btRows : Array ℕ :=
  #[13609019, 3590171, 11220553, 7325871, 5303242, 8495941, 8229684, 291466, 6054112, 7032137,
  9913147, 576711, 8417664, 4925402, 10717794, 6540178, 6638553, 1244592, 13108516, 2646976,
  4869204, 3961823, 9409019, 9258214]

end CFSG.Monster.Existence.Co1Bridge
