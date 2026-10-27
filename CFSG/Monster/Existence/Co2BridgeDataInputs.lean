module

public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
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

namespace CFSG.Monster.Existence.Co2Bridge

open CFSG.Sporadic.SmallF2.Native

@[expose] def xWord : List ℕ :=
  [5, 16, 1, 15, 5, 16, 1, 15, 5, 16, 1, 15, 5, 16, 1, 15, 5, 16, 1, 15]

@[expose] def yWord : List ℕ :=
  [23, 1, 23, 1, 23, 1, 16, 6, 19, 23, 16, 6, 19, 23, 16, 6, 19, 23, 16, 6,
    19, 23, 23, 1]

@[expose] def eRows : Array ℕ :=
  #[3293059, 1093243, 1996210, 3161391, 1589291, 812805, 3175192, 2855905, 463541, 760117,
    2575593, 1366206, 716318, 1371704, 3742922, 1549498, 2597373, 3850744, 3499680, 1176573,
    2805090, 3558424]

@[expose] def eInvRows : Array ℕ :=
  #[2721165, 26388, 2905883, 2610457, 1768004, 968261, 2169783, 3362407, 79502, 1893530,
    1129064, 1769593, 192982, 1079628, 481088, 2853836, 1692771, 2813619, 1019500, 1153706,
    1457215, 2301676]

@[expose] def atRows : Array ℕ :=
  #[2114050, 2114049, 1048584, 1048580, 415936, 3150720, 415888, 128, 3150496, 512, 1024, 2048,
    4096, 3473408, 16384, 917504, 3416064, 131072, 262144, 425984, 1048576, 2097152]

@[expose] def btRows : Array ℕ :=
  #[2097280, 2097154, 2097283, 3047424, 2621572, 3014664, 655360, 2621584, 2883584, 3014688,
    2228288, 2359552, 3015168, 2753536, 2361344, 3018752, 2097152, 2760704, 802816, 2621440,
    2686976, 1048576]

@[expose] def qMat (l : ℕ) : Array ℕ := CFSG.Monster.B.Co2.Native.genRecords[l]!.quotientMatrix

@[expose] def actWordQ : List ℕ → ℕ → ℕ
  | [], c => c
  | l :: w, c => actWordQ w (CFSG.Monster.B.Co2.Native.actD 22 (qMat l) c)

end CFSG.Monster.Existence.Co2Bridge
