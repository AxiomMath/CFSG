
module

public import CFSG.Monster.B.Short.Rootless
public import CFSG.Monster.B.TwoA.Census.PermCert
public import CFSG.Monster.B.TwoA.Unitary.NData
public import CFSG.Monster.VisQuot.Monomial
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
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

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.VisQuot CFSG.Monster.VisCert CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census

@[expose] def permRows24 : Array (Array ℕ) :=
  #[#[2109, 2110, 2857004, 2623544, 2971700, 3065884, 6392932, 15303820, 15465996, 7018276, 3132,
      123964, 4096, 8192, 16384, 32768, 65536, 262144, 520192, 11243520, 10395648, 11911168,
      2097152, 7163904],
    #[9013551, 9079084, 10586410, 9705742, 12523814, 9013566, 12378216, 9953448, 15254306,
      10584360, 9078824, 12823588, 4096, 8192, 16384, 32768, 131072, 262144, 65536, 2097152,
      524288, 1048576, 13922304, 7770112],
    #[9013551, 9079084, 10586410, 9013566, 9705742, 12523814, 12378216, 9953448, 6922762,
      15254306, 12823588, 4965388, 4096, 8192, 16384, 32768, 131072, 520192, 262144, 2097152,
      1048576, 3731456, 8388608, 13922304],
    #[1, 4, 16, 32, 8, 2, 12182080, 10089344, 8496896, 9013504, 256, 512, 4096, 8192, 16384,
      32768, 524288, 1048576, 2097152, 8388608, 11243520, 11911168, 13230080, 4194304],
    #[1, 2, 249, 396533, 267485, 137453, 189, 125, 12609024, 9013504, 2048, 1024, 4096, 8192,
      16384, 65536, 32768, 262144, 131072, 524288, 11243520, 13922304, 4194304, 13230080],
    #[4858996, 4854903, 5379185, 4854909, 7976021, 6390885, 5378160, 14545121, 256, 7443248,
      4858928, 9186324, 8192, 4096, 16384, 32768, 65536, 131072, 520192, 1048576, 524288,
      2097152, 4194304, 16400384]]

@[expose] def permRowOK (k : ℕ) : Bool :=
  (List.range 24).all fun j =>
    rowCheck (fun m => ellN j ((ainv n6PermArr[k]!)[m]!)) (permRows24[k]!)[j]!

@[expose] def permQuotOK (k : ℕ) : Bool :=
  (List.range 22).all fun t =>
    let x := VisCert.actRows permRows24[k]! Native.quotientBasis[t]! ^^^
      Native.actD 22 Native.quotientBasis (n6RowArr[k]!)[t]!
    x == 0 || x == 12288

@[expose] def wordActD : List ℕ → ℕ → ℕ
  | [], c => c
  | a :: w, c => wordActD w (Native.actD 22 (Native.genRecords[a]!).quotientMatrix c)

@[expose] def wordRowsOK (k : ℕ) : Bool :=
  (n6WordArr[k]!).all (fun a => decide (a < 24)) &&
    (List.range 22).all fun t => wordActD n6WordArr[k]! (1 <<< t) == (n6RowArr[k + 6]!)[t]!

end CFSG.Monster.B.TwoA.Unitary
