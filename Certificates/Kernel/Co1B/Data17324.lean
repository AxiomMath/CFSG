module

public import Certificates.Data.Kernel.SporSch.Co1MatW
public meta import Certificates.Kernel.Co1B.Gen17324
public meta import Certificates.Kernel.SporSch.Co1.GenDag
public import Certificates.Kernel.SporSch.Co1.GenDag
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

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17324.KA

@[expose] noncomputable def KW : List (List Nat) :=
  [[nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4],
    [nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 4], [nat_lit 8, nat_lit 7], [nat_lit 6, nat_lit 8], [nat_lit 10,
    nat_lit 12], [nat_lit 12, nat_lit 9], [nat_lit 6, nat_lit 8], [nat_lit 8, nat_lit 7],
    [nat_lit 16, nat_lit 20], [nat_lit 8, nat_lit 23], [nat_lit 22, nat_lit 8], [nat_lit 6,
    nat_lit 7], [nat_lit 18, nat_lit 6], [nat_lit 24, nat_lit 6], [nat_lit 20, nat_lit 9],
    [nat_lit 34, nat_lit 28], [nat_lit 32, nat_lit 26], [nat_lit 8, nat_lit 29], [nat_lit 14,
    nat_lit 41], [nat_lit 42, nat_lit 6], [nat_lit 6, nat_lit 8], [nat_lit 38, nat_lit 7],
    [nat_lit 44, nat_lit 41], [nat_lit 48, nat_lit 36], [nat_lit 28, nat_lit 30], [nat_lit 50,
    nat_lit 47], [nat_lit 30, nat_lit 26], [nat_lit 54, nat_lit 57], [nat_lit 56, nat_lit 41],
    [nat_lit 36, nat_lit 53], [nat_lit 40, nat_lit 64], [nat_lit 6, nat_lit 67], [nat_lit 58,
    nat_lit 62], [nat_lit 66, nat_lit 62], [nat_lit 52, nat_lit 65], [nat_lit 26, nat_lit 9],
    [nat_lit 46, nat_lit 9], [nat_lit 70, nat_lit 72], [nat_lit 78, nat_lit 73], [nat_lit 60,
    nat_lit 68], [nat_lit 80, nat_lit 85], [nat_lit 86, nat_lit 63], [nat_lit 8, nat_lit 82],
    [nat_lit 82, nat_lit 74], [nat_lit 90, nat_lit 77], [nat_lit 74, nat_lit 93], [nat_lit 68,
    nat_lit 76], [nat_lit 88, nat_lit 85], [nat_lit 96, nat_lit 62], [nat_lit 84, nat_lit 77],
    [nat_lit 104, nat_lit 101], [nat_lit 100, nat_lit 102], [nat_lit 72, nat_lit 108], [nat_lit 94,
    nat_lit 64], [nat_lit 110, nat_lit 92], [nat_lit 111, nat_lit 111, nat_lit 111, nat_lit 111,
    nat_lit 111, nat_lit 111, nat_lit 113, nat_lit 113, nat_lit 111, nat_lit 113, nat_lit 114],
    [nat_lit 62, nat_lit 76], [nat_lit 111, nat_lit 111, nat_lit 117, nat_lit 117, nat_lit 111,
    nat_lit 113, nat_lit 113, nat_lit 117, nat_lit 118], [nat_lit 76, nat_lit 92], [nat_lit 111,
    nat_lit 121, nat_lit 111, nat_lit 111, nat_lit 121, nat_lit 122], [nat_lit 117, nat_lit 117,
    nat_lit 117, nat_lit 117, nat_lit 117, nat_lit 121, nat_lit 117, nat_lit 117, nat_lit 117,
    nat_lit 121, nat_lit 121, nat_lit 124], [nat_lit 118, nat_lit 122], [nat_lit 111, nat_lit 111,
    nat_lit 113, nat_lit 127, nat_lit 111, nat_lit 127, nat_lit 128], [nat_lit 121, nat_lit 127,
    nat_lit 117, nat_lit 127, nat_lit 127, nat_lit 127, nat_lit 121, nat_lit 130], [nat_lit 112,
    nat_lit 108], [nat_lit 111, nat_lit 127, nat_lit 121, nat_lit 121, nat_lit 113, nat_lit 111,
    nat_lit 134], [nat_lit 117, nat_lit 117, nat_lit 127, nat_lit 121, nat_lit 121, nat_lit 127,
    nat_lit 117, nat_lit 136], [nat_lit 98, nat_lit 129], [nat_lit 111, nat_lit 113, nat_lit 133,
    nat_lit 139, nat_lit 111, nat_lit 127, nat_lit 140], [nat_lit 117, nat_lit 127, nat_lit 127,
    nat_lit 127, nat_lit 117, nat_lit 142], [nat_lit 139, nat_lit 127, nat_lit 139, nat_lit 127,
    nat_lit 133, nat_lit 144], [nat_lit 114, nat_lit 64], [nat_lit 113, nat_lit 147, nat_lit 117,
    nat_lit 139, nat_lit 127, nat_lit 148], [nat_lit 117, nat_lit 117, nat_lit 121, nat_lit 117,
    nat_lit 147, nat_lit 127, nat_lit 150], [nat_lit 127, nat_lit 127, nat_lit 139, nat_lit 152],
    [nat_lit 148, nat_lit 103], [nat_lit 113, nat_lit 147, nat_lit 133, nat_lit 121, nat_lit 111,
    nat_lit 156], [nat_lit 117, nat_lit 121, nat_lit 121, nat_lit 147, nat_lit 158], [nat_lit 127,
    nat_lit 133, nat_lit 147, nat_lit 133, nat_lit 160], [nat_lit 147, nat_lit 155, nat_lit 155,
    nat_lit 147, nat_lit 155, nat_lit 155, nat_lit 147, nat_lit 155, nat_lit 162], [nat_lit 106,
    nat_lit 122], [nat_lit 111, nat_lit 121, nat_lit 139, nat_lit 127, nat_lit 166], [nat_lit 121,
    nat_lit 117, nat_lit 139, nat_lit 168], [nat_lit 127, nat_lit 133, nat_lit 155, nat_lit 127,
    nat_lit 170], [nat_lit 147, nat_lit 165, nat_lit 165, nat_lit 147, nat_lit 165, nat_lit 172],
    [nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 126, nat_lit 110, nat_lit 120, nat_lit 120, nat_lit 110, nat_lit 132, nat_lit 116,
    nat_lit 120, nat_lit 120, nat_lit 116, nat_lit 126, nat_lit 126, nat_lit 132, nat_lit 154,
    nat_lit 154, nat_lit 164, nat_lit 164, nat_lit 146, nat_lit 164, nat_lit 174], [nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 4, nat_lit 110, nat_lit 120, nat_lit 174, nat_lit 110, nat_lit 154,
    nat_lit 132, nat_lit 120, nat_lit 146, nat_lit 116, nat_lit 126, nat_lit 138, nat_lit 126,
    nat_lit 174, nat_lit 154, nat_lit 154, nat_lit 174, nat_lit 164], [nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 112, nat_lit 120, nat_lit 112,
    nat_lit 110, nat_lit 110, nat_lit 146, nat_lit 154, nat_lit 132, nat_lit 116, nat_lit 164,
    nat_lit 132, nat_lit 174, nat_lit 132, nat_lit 146, nat_lit 154, nat_lit 174, nat_lit 146,
    nat_lit 174]]

@[expose] noncomputable def D0 : Nat :=
  nat_lit 1249461552060468467766996592682395739591214687597999395595346231782190682522824028104776597866001356357683199861284875613818928633379039195879026543187774589282202622654920

@[expose] noncomputable def T : List Nat :=
  [nat_lit 123665204422062557356803572788677631011309541569709136179232403901906511584503046599112559797157752258954946564622144514457573459535397137501359353526631510665794982588186625,
    nat_lit 101887585114647883726107312874460135527175656995341798678333508484716571984319735902981944431927512454655109585827198688930921903620921948853939358770393747096911698102342092,
    nat_lit 6141878836813386801110637642575461143887980343411924070390724115768906295300576855921021116054481391212873794054079111093643827765629589706952587233947505640669185812293648,
    nat_lit 230184297095283034371822335572071373002329408133001093345021458910366010940415388267040721862244253973870661471219554643479797072582362173041469357940572505034935009033170525,
    nat_lit 1382476588556537060948850327203726485765978446735868817432369141733817468051771257249523436637089747172436100952691225604807519313179572125791193191771590779072676142552960]

@[expose] noncomputable def Sel : List (List Nat) :=
  [[nat_lit 0], [nat_lit 5, nat_lit 2, nat_lit 7, nat_lit 3, nat_lit 1], [nat_lit 9, nat_lit 10,
    nat_lit 6, nat_lit 7], [nat_lit 16, nat_lit 17, nat_lit 6, nat_lit 11, nat_lit 12, nat_lit 3],
    [nat_lit 46, nat_lit 93, nat_lit 74], [nat_lit 166, nat_lit 189, nat_lit 188]]

@[expose] noncomputable def CFs : List (List (List Nat)) :=
  [[[nat_lit 2, nat_lit 0, nat_lit 0, nat_lit 1]], [[nat_lit 2, nat_lit 7844110, nat_lit 0,
    nat_lit 2], [nat_lit 2, nat_lit 7844110, nat_lit 0], [nat_lit 2, nat_lit 7844110, nat_lit 0,
    nat_lit 2, nat_lit 3], [nat_lit 3, nat_lit 7844110, nat_lit 1], [nat_lit 3, nat_lit 0,
    nat_lit 0, nat_lit 2]], [[nat_lit 2, nat_lit 9803856, nat_lit 0, nat_lit 2], [nat_lit 2,
    nat_lit 9803856, nat_lit 0, nat_lit 1, nat_lit 2], [nat_lit 2, nat_lit 7844110, nat_lit 1,
    nat_lit 3], [nat_lit 2, nat_lit 9803856, nat_lit 0]], [[nat_lit 2, nat_lit 9803856, nat_lit 0,
    nat_lit 2], [nat_lit 2, nat_lit 9803856, nat_lit 1, nat_lit 3], [nat_lit 3, nat_lit 7844110,
    nat_lit 0, nat_lit 2], [nat_lit 2, nat_lit 7844110, nat_lit 1, nat_lit 3], [nat_lit 3,
    nat_lit 7844110, nat_lit 0, nat_lit 1, nat_lit 3], [nat_lit 3, nat_lit 7844110, nat_lit 1]],
    [[nat_lit 2, nat_lit 13744049, nat_lit 0, nat_lit 2, nat_lit 3], [nat_lit 2, nat_lit 14708629,
    nat_lit 1, nat_lit 2, nat_lit 3], [nat_lit 3, nat_lit 1887679, nat_lit 1, nat_lit 2]],
    [[nat_lit 2, nat_lit 7305031, nat_lit 2], [nat_lit 2, nat_lit 11493466, nat_lit 2], [nat_lit 2,
    nat_lit 3502177, nat_lit 0, nat_lit 1, nat_lit 3]]]

@[expose] noncomputable def CNs : List (List Nat) :=
  [[nat_lit 2056, nat_lit 2165, nat_lit 2162, nat_lit 2109, nat_lit 2087, nat_lit 2030,
    nat_lit 2096, nat_lit 2092, nat_lit 2103], [nat_lit 13, nat_lit 11, nat_lit 8, nat_lit 8,
    nat_lit 10, nat_lit 6, nat_lit 5, nat_lit 12, nat_lit 7], [nat_lit 0, nat_lit 0, nat_lit 0,
    nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 1, nat_lit 0, nat_lit 0], [nat_lit 1, nat_lit 0,
    nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0], [nat_lit 0,
    nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 2],
    [nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 1, nat_lit 0, nat_lit 0, nat_lit 0,
    nat_lit 0]]

@[expose] noncomputable def NP : List Nat :=
  [nat_lit 1, nat_lit 2, nat_lit 1, nat_lit 1, nat_lit 1, nat_lit 1]

end CertificateChecks.KernelCo1B.Bound17324.KA

#kss_co1dag CertificateChecks.KernelCo1B.Bound17324.DA CertificateChecks.KernelCo1B.Bound17324.kDagA

end
