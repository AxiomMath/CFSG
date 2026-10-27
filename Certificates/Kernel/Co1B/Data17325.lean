module

public import Certificates.Data.Kernel.SporSch.Co1MatW
public meta import Certificates.Kernel.Co1B.Gen17325
public meta import Certificates.Kernel.SporSch.Co1.GenDag
public meta import Certificates.Kernel.SporSch.Co1.GenBfs
meta import Certificates.Kernel.Co1B.In17325
public import Certificates.Kernel.SporSch.Co1.GenBfs
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

namespace CertificateChecks.KernelCo1B.Bound17325.KB

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
    [nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 112, nat_lit 120, nat_lit 146, nat_lit 112, nat_lit 138, nat_lit 138, nat_lit 126,
    nat_lit 120, nat_lit 116, nat_lit 154, nat_lit 132, nat_lit 132, nat_lit 146, nat_lit 146,
    nat_lit 146, nat_lit 164], [nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 132,
    nat_lit 116, nat_lit 112, nat_lit 126, nat_lit 110, nat_lit 132, nat_lit 174, nat_lit 154,
    nat_lit 120, nat_lit 154, nat_lit 174, nat_lit 146, nat_lit 126, nat_lit 146, nat_lit 164,
    nat_lit 154, nat_lit 146, nat_lit 164, nat_lit 146, nat_lit 164, nat_lit 174], [nat_lit 2,
    nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 110, nat_lit 120, nat_lit 174, nat_lit 110, nat_lit 132, nat_lit 116,
    nat_lit 138, nat_lit 116, nat_lit 116, nat_lit 146, nat_lit 146, nat_lit 132, nat_lit 126,
    nat_lit 164, nat_lit 154, nat_lit 154, nat_lit 164, nat_lit 164, nat_lit 146, nat_lit 174,
    nat_lit 164], [nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 164, nat_lit 174, nat_lit 126, nat_lit 110,
    nat_lit 110, nat_lit 116, nat_lit 154, nat_lit 164, nat_lit 120, nat_lit 138, nat_lit 132,
    nat_lit 126, nat_lit 126, nat_lit 146, nat_lit 174, nat_lit 164, nat_lit 154, nat_lit 146,
    nat_lit 146, nat_lit 146, nat_lit 174, nat_lit 164]]

@[expose] noncomputable def D1 : Nat :=
  nat_lit 179037531342828743906567196024260253015898438798716470969597041996430027813508407684198452573176524710518320859079101603526517904873418742494824730009243794942896955543707260

@[expose] noncomputable def LI : List Nat :=
  [nat_lit 123665204422062557356803572788677631011309541569709136179232403901906511584503046599112559797157752258954946564622144514457573459535397137501359353526631510665794982588186625,
    nat_lit 49317562282030242772481951546955956905685988164162123103646099106755913354824880467439800561922337188762425002447793565659378026030782407736981423843490620719722506105983742,
    nat_lit 75589882927164774864192157355845756870231915719907137069434122266334826499983829500569420829836957812251383686955833891581990874973600933607838323396893016660465331774701803,
    nat_lit 220623748762811288871416830086831727447309893315179751939778349459705309251933973973532320492234152620513815655104784859362317081034161043561812393953760972235667740273318237,
    nat_lit 179165320259789691356248486431766043334572236232415279597165585940247877145682312311397409109238623199584362338156632898596599359916060748494994750592723145840411538272622933,
    nat_lit 199255087349227112547470605964817399170506427202915259792929329501599440296599075797699320937634335374300102865855649726403832302923362872849355931457349416204073241766281450,
    nat_lit 95412052221771492838853892908039413273448897684282726555833679649294211378231355147633381031723602610252004039508887980422751200622995171386002962171767511724958052011616097,
    nat_lit 208023305110461347018497444362132162985605831443499433001838377368020472767762310141298104975681451312060945221864330842396423522730561177836191163410040763552325449888533411,
    nat_lit 70128532599821784083481497766053508307041520461026086926335690643121377140250584913371725607857122085214996737648481369723444596050063182676863557354349785176307517939997316,
    nat_lit 133786375047213819835656593318464706962115556237431339155706505796809277093753867509742418465716046470458914681482428424408925046798671501526913135268080159047591601215376299,
    nat_lit 209044698039407355761445479251359116013083033836817759507835725197010043189253553884871931177687910277782294868448917138199020825501392866488338087251957077676802786677324202,
    nat_lit 219077256643834050195650918915501251995203703080233347247867149716096129583184853994164904346569726612397074376756527893866058186287466931689388054517760999383387904836511584,
    nat_lit 149271787214603426010963578454907293650199737601412694573996680040695306793842229273012336375399211104541742797575630939305553973386393184395700706243233299667336673668467926,
    nat_lit 233699745217869535006986169535377855726195985882368376070974436073802616405700720763779475815254510421635002718018874597318706735821839814081587900554090790943951082131964881,
    nat_lit 166949753621443720193258599027429375125724219766187932794577695812527926830375696915725697734852434213370850488079600872262593123895852346092317610752546520899603687668564953,
    nat_lit 178990428451827861242587022981170411104761999790841187097591484288990476394095760118642560942658023429116300950410171057821825514103692813849600206285796263213053176208866567,
    nat_lit 180300694779237740566291562106522696848126974882141714960550906821724584238053816083916930258728257689103525730160792358748679982872190769989811291275307401067945202826305227,
    nat_lit 145290433050918131154554154492142312718340782247108719847453592531016483600292845962693743647352707413473746371430802254856425153108650332142588322169965770829082288530995521,
    nat_lit 208085228970049906686683054885811344654246208030254752704701586259881262807997279360319388780266461226104489705204621345368239911414435690743175599000397163441216040902864881,
    nat_lit 205530962856049997764265296389497240859923899925332278044072772987752728957120628862943075633338689345873569185945089262277997344930919859433742664150851633286592894286810173,
    nat_lit 239845619368411487518378092759332911101124782606344201164117898915795617053100244278349503906611782477046005494208657091601342846793559049568794208643390607627268241397099447,
    nat_lit 37394624763329670887056462185465451158048041941024584133995225978961649973944077341196300599855006612573342220861492195420806304947174628694039642943015709703782031541258354,
    nat_lit 52646478941205875215286968229606571668987909717332147437607900719276273055192247618549138098773514369157089506504142689721531096073530831860703101052115768153788043400309597,
    nat_lit 89943992649757265076228564484707172750531509188550964690201943824566692403889877746157679333718562768719468054008753643333757679009207195585447336355598915421544984478491738,
    nat_lit 187644465220161066359436143980835275872657776208523860811277786417279695933015105063936139333386764754790403711601470607147094546970003030246795175481574973934487353402450,
    nat_lit 112689447548979758326332093323523945185179640375175878221305182032482801772283658954797590829756316350499675169475791995729587009379558936418301903245173791413303479421050401,
    nat_lit 75237727617535287894205855816758683991133951152691352141680118517793548726102253303075049967561224210504200832952729865543909380569214906236403583711434659478676264120853287,
    nat_lit 24501524289914328396862907371663215034041267400254618145397242966188182395008527784063785403975823436227830758961940045603908126615021602597499384752373632171856958897286939,
    nat_lit 14727363373494116053673433859713884450316284058997191899240715161597803775142955258707133885471162712833121171435149304579884826622191845404775832904072040015211971011761755,
    nat_lit 138392560424536092757378928871899235757878118143185406714926883274418194601627896846498947766798199006009110833687313149411323385554175834480313309548507023011716684511532634,
    nat_lit 217551044826261208523110545589916894741094219734569686557553987111073329847540276077820171575521275221236604093367701569035661877836049596542024702423099211994212992653484286,
    nat_lit 122623003076716259602965886718232573546877442682009991701984723487625328865646482134991502155861968877768937587714158447974282352112371428577814936834257089129398854894793177,
    nat_lit 58170041563390394426718493382813585312163620037997283222213935172534258513785832752110362388019064582775218703807145793084686400439275520115401758256271208965803372303107237,
    nat_lit 246222281247116701354392335103235688788829485097395884869794679042816776707235309601428059349415022383764798344211245488788417483510395462896644548999236876636985838336939402,
    nat_lit 198902924668577484271429928227434231725990788770895069332247967375421573038786894029164257205130509527526709480592259911908048996129596521349345421964277668805611046603694886,
    nat_lit 239114121302937590873374635412054202344046572798768211550026877244084198256615786142667904387074279021245854736965398715862949486799862024049278219951935419665686188394216940,
    nat_lit 246288200127758236306664834949397241860908709695630761435122723933302018864434049902446872724366494716016604684983737172313391232150886695276799521470643276651259319224676824,
    nat_lit 189804834884518166576158609445790920019866122308763480111491529804824870672783073459802366611116128709371968369721910329394089254939778933957013951897634979287320400439537426,
    nat_lit 181835238614432590803949112574509816040551024726768455824329464044949516272308495596629953540815240019383071819450023041908236781494755910645274451145388507008158369182663844,
    nat_lit 122557084196074724650693386872071020474798218257066971019207607320795560214485750267400217314330577341713888520710922600360392036680446370212349554217091687513306249836303755,
    nat_lit 18498410666807525137567754206346248243977821472569979560967088486609081610446357819979248261288427870647616852586728299150583360501502727878331286040099121018723498355877041,
    nat_lit 75407192543515019468734254697902176129072061476565840556450348325375640262973880137314387090785724812486156684856877199024241584425774857219295476334954673181271572054271161,
    nat_lit 93885847775219231819405050577731543427717675856016611452973472361327136437155879459556914863409099674823772711730061016059131515006052955079876240197412367424727355846582527,
    nat_lit 47246948091505002290148113170432877050910808762103816770370815798330549541435429273905140570980915696052967998394632506981825339205976230527376167121659728848152668272809312,
    nat_lit 27156648949161234209414273403911398665592874144305434542815269298641843086951769739539693241851785260011662347423853937509395202705375218884497663394485862146892224501461738,
    nat_lit 40908243257437774719079986730284759950847286588810101994469702494958396575074380286937657097315620908986074680035874453434069296040220040600435495902431128894002884027186661,
    nat_lit 3792491918165815083336911997820272787979463517839344046362717357236803491399927838081335304996629111827628197063017994341538327912863769969916306633211456011067836605548446,
    nat_lit 45468971609834571988393823669260216432491612697067593775357456296147581096104692331618173127531292478889238220462662072184937177373262107355399901209456976492989765389918228,
    nat_lit 170849292311176803839985679659356273045200972645438938336531198385229762758539176377420388213232250865577014542908125268631874816927999438726015462289241463222340988633149747,
    nat_lit 233837839800850329053839204180687790619009664543025008738980926220979644993410273156506815852301662242152460615901852661963825998119229818410366404244504876605384763044529231,
    nat_lit 142163615088870082494371326994828769970892613354525910030786490770750832304858132114362571774273648509781586375306147603038501618096965465159773470464244820971754394343728304,
    nat_lit 199072396965577357152012703306873818429346573132865819162496484284295727565900541216617836370721301822411252426765346045764554910810915121303771737745874971700214413155886264,
    nat_lit 209103777095016509014542191155042936249022981461080851446190233809346316237764444248078855656750582081904456235770954047740768924329762158180906954833467664715598978780159480,
    nat_lit 40318913235522886119369077601658495118615602288568790114281468363602243506690006679361670350346760661207428784492244122377033148311131952244483418650497695322691001700792955,
    nat_lit 52459306502781281783448619873974313063254590219129215481397907741422966405805001349917296566557670116429151479416518618401894725938277372249493372531959294951012879933394703,
    nat_lit 192841329126984774995368737257762029751787276280074718629312222146708307279998653704702896870174313650821164043291122673928964477955139020518115915922356814432764170117687436,
    nat_lit 45535377437820554740396716934638772954683747697603480632449986107811931951548465512307651889008710252005884746520135073327897379747323542046944208054494446603704147333317702,
    nat_lit 106274638238510554263167854029390497801093340767986625561338069663483809250159548422802463599109542147346194280139380051467215244880579343257484434521525551405984455154692410,
    nat_lit 233644189466803412467146335896266828141623099835595058028431962553165340801890922739739715252948170474442811536539712419489366754005803796273957825755596198526325298724726659,
    nat_lit 64604056095290048137915079045281096033281083181188996046204907945019894980327721206248313488608499991890795928360604880471996201380464917476584669572582875897072492891403644]

@[expose] noncomputable def CW : List Nat :=
  [nat_lit 26, nat_lit 31, nat_lit 5, nat_lit 56]

@[expose] noncomputable def T : List Nat :=
  [nat_lit 123665204422062557356803572788677631011309541569709136179232403901906511584503046599112559797157752258954946564622144514457573459535397137501359353526631510665794982588186625,
    nat_lit 129339856391079681820948087962913678722290862506696042983381613304505494333695329562300712927853859743072952360832784211459189257201542842449077431756217649009321547719889044,
    nat_lit 73567998700975391413593845492968708354074091617225431403838980464107630028378588711038175949141953382381439646244011096819889233519508952635797454126877356172570841932494901,
    nat_lit 242215633235413374493350874219930777540567743588503239801142873604193152219462163186218139804894739880771573136181715972993548051407382171855393431782792959951115073489616121,
    nat_lit 133026096586959362589545216041467448984978822376375623691794186240539111556484471415911267367897948370584445646443820263613640914282041463672019151527205040953564628753241440]

@[expose] noncomputable def Sel : List (List Nat) :=
  [[nat_lit 2, nat_lit 3], [nat_lit 23, nat_lit 25, nat_lit 0, nat_lit 7, nat_lit 1], [nat_lit 22,
    nat_lit 25, nat_lit 26], [nat_lit 15, nat_lit 2, nat_lit 9, nat_lit 3], [nat_lit 118,
    nat_lit 99, nat_lit 101, nat_lit 3, nat_lit 95, nat_lit 22], [nat_lit 37, nat_lit 49,
    nat_lit 36, nat_lit 0, nat_lit 3, nat_lit 29, nat_lit 50], [nat_lit 16, nat_lit 17, nat_lit 4,
    nat_lit 0, nat_lit 6, nat_lit 10], [nat_lit 87, nat_lit 83, nat_lit 0, nat_lit 2, nat_lit 1]]

@[expose] noncomputable def CFs : List (List (List Nat)) :=
  [[[nat_lit 2, nat_lit 0, nat_lit 0, nat_lit 1, nat_lit 2], [nat_lit 3, nat_lit 0, nat_lit 0,
    nat_lit 1, nat_lit 2, nat_lit 3, nat_lit 4]], [[nat_lit 2, nat_lit 14139972, nat_lit 2,
    nat_lit 4], [nat_lit 2, nat_lit 16131808, nat_lit 0, nat_lit 1], [nat_lit 3, nat_lit 0,
    nat_lit 0, nat_lit 1], [nat_lit 3, nat_lit 14139972, nat_lit 2], [nat_lit 3, nat_lit 0,
    nat_lit 0, nat_lit 2]], [[nat_lit 2, nat_lit 14139972, nat_lit 0, nat_lit 1, nat_lit 4],
    [nat_lit 2, nat_lit 10832440, nat_lit 2], [nat_lit 2, nat_lit 16131808, nat_lit 0]],
    [[nat_lit 2, nat_lit 460543, nat_lit 1, nat_lit 3, nat_lit 4], [nat_lit 2, nat_lit 0,
    nat_lit 0, nat_lit 1, nat_lit 2], [nat_lit 2, nat_lit 14139972, nat_lit 1, nat_lit 2],
    [nat_lit 3, nat_lit 0, nat_lit 0, nat_lit 1, nat_lit 2, nat_lit 3, nat_lit 4]], [[nat_lit 2,
    nat_lit 10873499, nat_lit 0, nat_lit 1, nat_lit 2, nat_lit 3], [nat_lit 2, nat_lit 15980561,
    nat_lit 2], [nat_lit 2, nat_lit 15980561, nat_lit 3], [nat_lit 3, nat_lit 0, nat_lit 0,
    nat_lit 1, nat_lit 2, nat_lit 3, nat_lit 4], [nat_lit 3, nat_lit 460543, nat_lit 0, nat_lit 1,
    nat_lit 2, nat_lit 3, nat_lit 4], [nat_lit 3, nat_lit 14139972, nat_lit 0, nat_lit 1,
    nat_lit 4]], [[nat_lit 2, nat_lit 10832440, nat_lit 0, nat_lit 1], [nat_lit 2,
    nat_lit 15980561, nat_lit 0], [nat_lit 2, nat_lit 10832440, nat_lit 1], [nat_lit 3, nat_lit 0,
    nat_lit 0, nat_lit 1], [nat_lit 3, nat_lit 0, nat_lit 0, nat_lit 1, nat_lit 2, nat_lit 3,
    nat_lit 4], [nat_lit 3, nat_lit 14139972, nat_lit 1, nat_lit 3, nat_lit 4], [nat_lit 3,
    nat_lit 8496801, nat_lit 0, nat_lit 2]], [[nat_lit 2, nat_lit 460543, nat_lit 0, nat_lit 1],
    [nat_lit 2, nat_lit 12695471, nat_lit 0], [nat_lit 2, nat_lit 14139972, nat_lit 1], [nat_lit 2,
    nat_lit 0, nat_lit 0, nat_lit 1], [nat_lit 3, nat_lit 14139972, nat_lit 2], [nat_lit 3,
    nat_lit 10832440, nat_lit 2, nat_lit 3]], [[nat_lit 2, nat_lit 7118979, nat_lit 0, nat_lit 1,
    nat_lit 4], [nat_lit 2, nat_lit 12695471, nat_lit 3], [nat_lit 2, nat_lit 0, nat_lit 0,
    nat_lit 1], [nat_lit 3, nat_lit 0, nat_lit 0, nat_lit 1, nat_lit 2], [nat_lit 3, nat_lit 0,
    nat_lit 0, nat_lit 2]]]

@[expose] noncomputable def CNs : List (List Nat) :=
  [[nat_lit 172, nat_lit 186, nat_lit 169, nat_lit 157, nat_lit 153, nat_lit 162, nat_lit 177,
    nat_lit 166, nat_lit 158], [nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 3, nat_lit 0, nat_lit 0,
    nat_lit 1, nat_lit 1, nat_lit 1], [nat_lit 0, nat_lit 1, nat_lit 0, nat_lit 0, nat_lit 1,
    nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0], [nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 1,
    nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0], [nat_lit 0, nat_lit 0, nat_lit 1,
    nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 1, nat_lit 0, nat_lit 0], [nat_lit 0, nat_lit 0,
    nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 1, nat_lit 0], [nat_lit 0,
    nat_lit 0, nat_lit 1, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0],
    [nat_lit 0, nat_lit 0, nat_lit 1, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0,
    nat_lit 0]]

@[expose] noncomputable def NP : List Nat :=
  [nat_lit 1, nat_lit 1, nat_lit 1, nat_lit 1, nat_lit 1, nat_lit 1, nat_lit 1, nat_lit 1]

@[expose] noncomputable def T2 : List Nat :=
  [nat_lit 129339856391079681820948087962913678722290862506696042983381613304505494333695329562300712927853859743072952360832784211459189257201542842449077431756217649009321547719889044,
    nat_lit 120575345497799445882528615646560414138867109868610371443804018795988311770610528983434485496923531483586434844761926999380787303089877004364721656461656519319675665985127644,
    nat_lit 234461233727197515915536943861239373247104876659321791574567408979696085716842859603603366954874572932362002515756382901869878799325258889226477063939000586195547599171920482,
    nat_lit 166486192198704060975376625193231393598451368209181435796123677251544914519585811470856344636753118453155173928272529718336112804243589369502581679379846786672748105382580294,
    nat_lit 184044972913007073803684444263180766558937837495733657388522001668615724537082992470433427104346873005282120403460992697662828980265386637787410962307249724021703792608146199]

@[expose] noncomputable def Sel2 : List (List Nat) :=
  [[nat_lit 19, nat_lit 21, nat_lit 20, nat_lit 13, nat_lit 1], [nat_lit 223, nat_lit 2,
    nat_lit 10, nat_lit 12, nat_lit 11, nat_lit 1, nat_lit 5, nat_lit 14, nat_lit 9, nat_lit 16,
    nat_lit 20, nat_lit 58, nat_lit 88, nat_lit 109, nat_lit 155, nat_lit 171], [nat_lit 9,
    nat_lit 13, nat_lit 12, nat_lit 11], [nat_lit 58, nat_lit 64, nat_lit 9], [nat_lit 170,
    nat_lit 281, nat_lit 13, nat_lit 6, nat_lit 225, nat_lit 270, nat_lit 4, nat_lit 11,
    nat_lit 85, nat_lit 17, nat_lit 141, nat_lit 235, nat_lit 191, nat_lit 263, nat_lit 269,
    nat_lit 23, nat_lit 39, nat_lit 60, nat_lit 87, nat_lit 215, nat_lit 220, nat_lit 2,
    nat_lit 25, nat_lit 84, nat_lit 136, nat_lit 185, nat_lit 217, nat_lit 247, nat_lit 251],
    [nat_lit 167, nat_lit 171, nat_lit 125, nat_lit 6, nat_lit 11]]

@[expose] noncomputable def CFs2 : List (List (List Nat)) :=
  [[[nat_lit 2, nat_lit 0, nat_lit 0, nat_lit 1, nat_lit 3, nat_lit 4], [nat_lit 2, nat_lit 0,
    nat_lit 0, nat_lit 1, nat_lit 2, nat_lit 3, nat_lit 4], [nat_lit 3, nat_lit 0, nat_lit 1,
    nat_lit 2, nat_lit 3, nat_lit 4], [nat_lit 3, nat_lit 0, nat_lit 2, nat_lit 4], [nat_lit 3,
    nat_lit 0, nat_lit 0, nat_lit 2]], [[nat_lit 2, nat_lit 3563640, nat_lit 0, nat_lit 1,
    nat_lit 2, nat_lit 4], [nat_lit 2, nat_lit 0, nat_lit 1, nat_lit 2], [nat_lit 2, nat_lit 0,
    nat_lit 2, nat_lit 4], [nat_lit 3, nat_lit 0, nat_lit 3, nat_lit 4], [nat_lit 3, nat_lit 0,
    nat_lit 1, nat_lit 2, nat_lit 4], [nat_lit 3, nat_lit 0, nat_lit 0, nat_lit 2], [nat_lit 3,
    nat_lit 0, nat_lit 1, nat_lit 3], [nat_lit 3, nat_lit 0, nat_lit 2, nat_lit 3, nat_lit 4],
    [nat_lit 3, nat_lit 0, nat_lit 1, nat_lit 4], [nat_lit 3, nat_lit 9401560, nat_lit 0],
    [nat_lit 3, nat_lit 9401560, nat_lit 1, nat_lit 2], [nat_lit 3, nat_lit 1245395, nat_lit 0],
    [nat_lit 3, nat_lit 4677735, nat_lit 0, nat_lit 1, nat_lit 4], [nat_lit 3, nat_lit 123437,
    nat_lit 2, nat_lit 4], [nat_lit 3, nat_lit 12121741, nat_lit 0, nat_lit 1], [nat_lit 3,
    nat_lit 13112511, nat_lit 0, nat_lit 1, nat_lit 2, nat_lit 4]], [[nat_lit 0, nat_lit 0,
    nat_lit 2, nat_lit 4], [nat_lit 2, nat_lit 2392710, nat_lit 1, nat_lit 2, nat_lit 3],
    [nat_lit 2, nat_lit 9401560, nat_lit 1, nat_lit 3], [nat_lit 3, nat_lit 9401560, nat_lit 3]],
    [[nat_lit 2, nat_lit 2392710, nat_lit 0, nat_lit 3], [nat_lit 2, nat_lit 123437, nat_lit 1,
    nat_lit 2, nat_lit 4], [nat_lit 3, nat_lit 0, nat_lit 1, nat_lit 4]], [[nat_lit 2,
    nat_lit 5915650, nat_lit 1], [nat_lit 2, nat_lit 7224779, nat_lit 2], [nat_lit 3, nat_lit 0,
    nat_lit 2, nat_lit 4], [nat_lit 3, nat_lit 0, nat_lit 2, nat_lit 3], [nat_lit 3,
    nat_lit 1015967, nat_lit 4], [nat_lit 3, nat_lit 15066210, nat_lit 1], [nat_lit 3, nat_lit 0,
    nat_lit 1, nat_lit 3], [nat_lit 3, nat_lit 0, nat_lit 1, nat_lit 4], [nat_lit 3,
    nat_lit 1245395, nat_lit 1], [nat_lit 3, nat_lit 0, nat_lit 3, nat_lit 4], [nat_lit 3,
    nat_lit 123437, nat_lit 0], [nat_lit 3, nat_lit 3830790, nat_lit 3], [nat_lit 3,
    nat_lit 10694405, nat_lit 3], [nat_lit 3, nat_lit 16220955, nat_lit 2, nat_lit 3, nat_lit 4],
    [nat_lit 3, nat_lit 15066210, nat_lit 0], [nat_lit 3, nat_lit 0, nat_lit 0, nat_lit 1,
    nat_lit 2, nat_lit 3, nat_lit 4], [nat_lit 3, nat_lit 9401560, nat_lit 4], [nat_lit 3,
    nat_lit 2392710, nat_lit 3], [nat_lit 3, nat_lit 1245395, nat_lit 0, nat_lit 2], [nat_lit 3,
    nat_lit 3573956, nat_lit 1, nat_lit 2, nat_lit 4], [nat_lit 3, nat_lit 1015967, nat_lit 2],
    [nat_lit 3, nat_lit 0, nat_lit 1, nat_lit 2], [nat_lit 3, nat_lit 9401560, nat_lit 1],
    [nat_lit 3, nat_lit 1245395, nat_lit 0], [nat_lit 3, nat_lit 4677735, nat_lit 0, nat_lit 1,
    nat_lit 3, nat_lit 4], [nat_lit 3, nat_lit 5915650, nat_lit 0, nat_lit 1, nat_lit 3,
    nat_lit 4], [nat_lit 3, nat_lit 3573956, nat_lit 0, nat_lit 1, nat_lit 3, nat_lit 4],
    [nat_lit 3, nat_lit 7075757, nat_lit 0, nat_lit 1, nat_lit 2, nat_lit 3, nat_lit 4],
    [nat_lit 3, nat_lit 1100345, nat_lit 0, nat_lit 1, nat_lit 2]], [[nat_lit 2, nat_lit 5915650,
    nat_lit 1, nat_lit 2, nat_lit 4], [nat_lit 2, nat_lit 3830790, nat_lit 0], [nat_lit 2,
    nat_lit 4677735, nat_lit 4], [nat_lit 3, nat_lit 0, nat_lit 2, nat_lit 3], [nat_lit 3,
    nat_lit 0, nat_lit 1, nat_lit 4]]]

@[expose] noncomputable def CNs2 : List (List Nat) :=
  [[nat_lit 1, nat_lit 1, nat_lit 1, nat_lit 1, nat_lit 0, nat_lit 0, nat_lit 1, nat_lit 0,
    nat_lit 0], [nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0,
    nat_lit 0, nat_lit 1], [nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0,
    nat_lit 0, nat_lit 0, nat_lit 1], [nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0,
    nat_lit 0, nat_lit 0, nat_lit 1, nat_lit 0], [nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0,
    nat_lit 0, nat_lit 1, nat_lit 0, nat_lit 0, nat_lit 0], [nat_lit 0, nat_lit 0, nat_lit 0,
    nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 1, nat_lit 0, nat_lit 0]]

@[expose] noncomputable def NP2 : List Nat :=
  [nat_lit 1, nat_lit 1, nat_lit 1, nat_lit 1, nat_lit 2, nat_lit 1]

end CertificateChecks.KernelCo1B.Bound17325.KB

#kss_co1dag CertificateChecks.KernelCo1B.Bound17325.DB CertificateChecks.KernelCo1B.Bound17325.kDagB

#kss_co1gt CertificateChecks.KernelCo1B.Bound17325.LT CertificateChecks.KernelCo1B.Bound17325.lArr 200

#kss_co1gt CertificateChecks.KernelCo1B.Bound17325.ET CertificateChecks.KernelCo1B.Bound17325.eArr 40000

end
