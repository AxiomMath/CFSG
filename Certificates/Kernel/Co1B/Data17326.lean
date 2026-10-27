module

public import Certificates.Data.Kernel.SporSch.Co1MatW
public meta import Certificates.Kernel.Co1B.Gen17326
public meta import Certificates.Kernel.SporSch.Co1.GenDag
public meta import Certificates.Kernel.SporSch.Co1.GenBfs
meta import Certificates.Kernel.Co1B.In17326
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

namespace CertificateChecks.KernelCo1B.Bound17326.KC

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
    [nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 110, nat_lit 126, nat_lit 174, nat_lit 146,
    nat_lit 112, nat_lit 120, nat_lit 174, nat_lit 138, nat_lit 116, nat_lit 138, nat_lit 126,
    nat_lit 138, nat_lit 174, nat_lit 164, nat_lit 154, nat_lit 154, nat_lit 164, nat_lit 146,
    nat_lit 174, nat_lit 164], [nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 4, nat_lit 126, nat_lit 110, nat_lit 110, nat_lit 116, nat_lit 110,
    nat_lit 164, nat_lit 116, nat_lit 164, nat_lit 126, nat_lit 120, nat_lit 126, nat_lit 126,
    nat_lit 132, nat_lit 138, nat_lit 174, nat_lit 154, nat_lit 164, nat_lit 146, nat_lit 154,
    nat_lit 174, nat_lit 164], [nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 112, nat_lit 110, nat_lit 116, nat_lit 116, nat_lit 110,
    nat_lit 126, nat_lit 164, nat_lit 120, nat_lit 126, nat_lit 116, nat_lit 138, nat_lit 132,
    nat_lit 164, nat_lit 126, nat_lit 126, nat_lit 154, nat_lit 146, nat_lit 146, nat_lit 174,
    nat_lit 164, nat_lit 146, nat_lit 146, nat_lit 174, nat_lit 164, nat_lit 164], [nat_lit 2,
    nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 126, nat_lit 146, nat_lit 138,
    nat_lit 110, nat_lit 110, nat_lit 164, nat_lit 174, nat_lit 126, nat_lit 138, nat_lit 116,
    nat_lit 154, nat_lit 126, nat_lit 126, nat_lit 126, nat_lit 146, nat_lit 146, nat_lit 146,
    nat_lit 164, nat_lit 174], [nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4,
    nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2,
    nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 4, nat_lit 4, nat_lit 2, nat_lit 4,
    nat_lit 2, nat_lit 132, nat_lit 112, nat_lit 120, nat_lit 120, nat_lit 112, nat_lit 132,
    nat_lit 146, nat_lit 132, nat_lit 116, nat_lit 164, nat_lit 126, nat_lit 174, nat_lit 126,
    nat_lit 154, nat_lit 174, nat_lit 146, nat_lit 164, nat_lit 146, nat_lit 164]]

@[expose] noncomputable def Z0 : Nat :=
  nat_lit 102578478008740563414304789160399870425594051114838039200359693282097940190874398721743515290787208239293159828591441410197832757524052579455136137078472427355943433567645287

@[expose] noncomputable def T : List Nat :=
  [nat_lit 123665204422062557356803572788677631011309541569709136179232403901906511584503046599112559797157752258954946564622144514457573459535397137501359353526631510665794982588186625,
    nat_lit 119345575972817097344408075747577753046128373945749134637985441732845924456732414406735373330675119226515130392006075774964081926813484425896760453074851447862836747268690433,
    nat_lit 41506688181325016610333489903008030671563408692262159944416784566485410051898319138554345065365869141228022760633078478732345594546806889000191853806986369258231737100718186,
    nat_lit 132513453160467894442069415332475055707091697712055310280193222170242332158625029946539084337005724444938163016687820410324108558746260762926626181221782777143194099626990729,
    nat_lit 233377451262168565282061010900787877530628453799479144113751547593255131014505013490158660931068501448617681537189300104721013438290780829487001941985713721421364374611565923]

@[expose] noncomputable def Sel : List (List Nat) :=
  [[nat_lit 0, nat_lit 1, nat_lit 2], [nat_lit 17, nat_lit 16, nat_lit 8, nat_lit 0], [nat_lit 14,
    nat_lit 17, nat_lit 3, nat_lit 16], [nat_lit 0, nat_lit 9, nat_lit 4, nat_lit 10, nat_lit 3,
    nat_lit 8], [nat_lit 7, nat_lit 15, nat_lit 6, nat_lit 5, nat_lit 4, nat_lit 13], [nat_lit 17,
    nat_lit 32, nat_lit 16, nat_lit 29, nat_lit 31, nat_lit 33, nat_lit 18], [nat_lit 294,
    nat_lit 296, nat_lit 289]]

@[expose] noncomputable def CFs : List (List (List Nat)) :=
  [[[nat_lit 2, nat_lit 0, nat_lit 0, nat_lit 1], [nat_lit 3, nat_lit 0, nat_lit 0, nat_lit 1,
    nat_lit 2], [nat_lit 3, nat_lit 0, nat_lit 0, nat_lit 1, nat_lit 3]], [[nat_lit 2,
    nat_lit 8011569, nat_lit 1, nat_lit 2, nat_lit 4], [nat_lit 2, nat_lit 8011569, nat_lit 0,
    nat_lit 1, nat_lit 2, nat_lit 3], [nat_lit 2, nat_lit 8011569, nat_lit 2], [nat_lit 3,
    nat_lit 0, nat_lit 0, nat_lit 1]], [[nat_lit 2, nat_lit 8011569, nat_lit 0, nat_lit 1,
    nat_lit 2, nat_lit 4], [nat_lit 2, nat_lit 2461520, nat_lit 0], [nat_lit 2, nat_lit 0,
    nat_lit 0, nat_lit 1, nat_lit 2, nat_lit 3], [nat_lit 2, nat_lit 8011569, nat_lit 0, nat_lit 2,
    nat_lit 3, nat_lit 4]], [[nat_lit 2, nat_lit 0, nat_lit 0, nat_lit 1], [nat_lit 2,
    nat_lit 2461520, nat_lit 0], [nat_lit 2, nat_lit 8011569, nat_lit 1], [nat_lit 2,
    nat_lit 2461520, nat_lit 1], [nat_lit 3, nat_lit 8011569, nat_lit 0], [nat_lit 3,
    nat_lit 8011569, nat_lit 0, nat_lit 4]], [[nat_lit 2, nat_lit 8011569, nat_lit 0, nat_lit 1],
    [nat_lit 2, nat_lit 2461520, nat_lit 4], [nat_lit 3, nat_lit 8011569, nat_lit 1], [nat_lit 2,
    nat_lit 8011569, nat_lit 0], [nat_lit 3, nat_lit 0, nat_lit 0, nat_lit 1, nat_lit 2, nat_lit 3,
    nat_lit 4], [nat_lit 3, nat_lit 2461520, nat_lit 1, nat_lit 2, nat_lit 3]], [[nat_lit 2,
    nat_lit 8011569, nat_lit 1, nat_lit 2, nat_lit 3], [nat_lit 2, nat_lit 15663850, nat_lit 1,
    nat_lit 2, nat_lit 3], [nat_lit 2, nat_lit 8011569, nat_lit 2, nat_lit 3], [nat_lit 3,
    nat_lit 10441855, nat_lit 3], [nat_lit 2, nat_lit 15663850, nat_lit 0, nat_lit 1, nat_lit 2],
    [nat_lit 3, nat_lit 530665, nat_lit 3, nat_lit 4], [nat_lit 3, nat_lit 8011569, nat_lit 4]],
    [[nat_lit 2, nat_lit 16749173, nat_lit 2, nat_lit 3, nat_lit 4], [nat_lit 2, nat_lit 5981693,
    nat_lit 0, nat_lit 4], [nat_lit 2, nat_lit 16749173, nat_lit 2, nat_lit 3]]]

@[expose] noncomputable def CNs : List (List Nat) :=
  [[nat_lit 84, nat_lit 88, nat_lit 79, nat_lit 74, nat_lit 76, nat_lit 87, nat_lit 86, nat_lit 94,
    nat_lit 82], [nat_lit 0, nat_lit 1, nat_lit 1, nat_lit 2, nat_lit 3, nat_lit 0, nat_lit 1,
    nat_lit 0, nat_lit 2], [nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0,
    nat_lit 0, nat_lit 1, nat_lit 0], [nat_lit 0, nat_lit 1, nat_lit 0, nat_lit 0, nat_lit 0,
    nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0], [nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 1,
    nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0], [nat_lit 0, nat_lit 0, nat_lit 2,
    nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0], [nat_lit 0, nat_lit 0,
    nat_lit 0, nat_lit 0, nat_lit 1, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0]]

@[expose] noncomputable def NP : List Nat :=
  [nat_lit 3, nat_lit 1, nat_lit 1, nat_lit 2, nat_lit 1, nat_lit 1, nat_lit 1]

@[expose] noncomputable def T2 : List Nat :=
  [nat_lit 119345575972817097344408075747577753046128373945749134637985441732845924456732414406735373330675119226515130392006075774964081926813484425896760453074851447862836747268690433,
    nat_lit 49515672329692961327961282330045076247908239735994664459184636375295293773473634340973165945180708549595417541343427280468496774973910227051317169732283367573272826481272199,
    nat_lit 102119494180307820289824429605761003642509025635674190307968931562998865013363927864194403217500612467843128955964653975532677481525205972077992125744392268649830683146000047,
    nat_lit 172208975429472048863467668878127657517944684519177003963124154779161579416910377591886195551496732498392905922207760792621556386728166534799331238903000308417013950704872574,
    nat_lit 207954164819980632247574155451846525795562864749791378329229583556930153396868891263167738474363612753293536009593140480632974404186208509859014725788180345677921221397578578,
    nat_lit 172578221134518915515158238173361236050403497076727482581663756145995507365985415836232623807203867847837235789432713756186484571059058513281218917840087759149910617724298147,
    nat_lit 127959249415251548160192008005613484459405627660740942992060035706676993689701196474932517952415428227022159313883490914777911492550094889875774229389020627802429375568974033]

@[expose] noncomputable def Sel2 : List (List Nat) :=
  [[nat_lit 26, nat_lit 0, nat_lit 4, nat_lit 21, nat_lit 1, nat_lit 5], [nat_lit 27, nat_lit 12,
    nat_lit 1, nat_lit 11, nat_lit 5, nat_lit 25], [nat_lit 46, nat_lit 47, nat_lit 12,
    nat_lit 43], [nat_lit 108, nat_lit 54, nat_lit 25, nat_lit 24, nat_lit 2, nat_lit 12,
    nat_lit 14, nat_lit 17, nat_lit 104, nat_lit 27, nat_lit 109, nat_lit 110, nat_lit 5]]

@[expose] noncomputable def CFs2 : List (List (List Nat)) :=
  [[[nat_lit 2, nat_lit 0, nat_lit 0, nat_lit 3, nat_lit 5], [nat_lit 2, nat_lit 0, nat_lit 0,
    nat_lit 1], [nat_lit 3, nat_lit 0, nat_lit 0, nat_lit 3], [nat_lit 3, nat_lit 0, nat_lit 0,
    nat_lit 5], [nat_lit 3, nat_lit 0, nat_lit 0, nat_lit 2], [nat_lit 3, nat_lit 0, nat_lit 1,
    nat_lit 3]], [[nat_lit 2, nat_lit 13605119, nat_lit 0, nat_lit 2], [nat_lit 2, nat_lit 0,
    nat_lit 1, nat_lit 4], [nat_lit 3, nat_lit 0, nat_lit 0, nat_lit 2], [nat_lit 2, nat_lit 0,
    nat_lit 0, nat_lit 4], [nat_lit 3, nat_lit 0, nat_lit 1, nat_lit 3], [nat_lit 2, nat_lit 0,
    nat_lit 0, nat_lit 6]], [[nat_lit 2, nat_lit 0, nat_lit 3, nat_lit 4, nat_lit 6], [nat_lit 2,
    nat_lit 13605119, nat_lit 0], [nat_lit 2, nat_lit 0, nat_lit 1, nat_lit 4], [nat_lit 3,
    nat_lit 0, nat_lit 4, nat_lit 6]], [[nat_lit 2, nat_lit 13605119, nat_lit 0, nat_lit 1,
    nat_lit 2, nat_lit 4], [nat_lit 2, nat_lit 0, nat_lit 1, nat_lit 6], [nat_lit 3, nat_lit 0,
    nat_lit 1, nat_lit 5], [nat_lit 3, nat_lit 0, nat_lit 0, nat_lit 5], [nat_lit 3, nat_lit 0,
    nat_lit 1, nat_lit 2], [nat_lit 3, nat_lit 0, nat_lit 1, nat_lit 4], [nat_lit 3, nat_lit 0,
    nat_lit 2, nat_lit 4], [nat_lit 3, nat_lit 0, nat_lit 0, nat_lit 1, nat_lit 2, nat_lit 4],
    [nat_lit 3, nat_lit 13605119, nat_lit 0, nat_lit 1, nat_lit 4], [nat_lit 3, nat_lit 0,
    nat_lit 2, nat_lit 5], [nat_lit 3, nat_lit 13605119, nat_lit 0, nat_lit 1, nat_lit 2,
    nat_lit 3, nat_lit 4], [nat_lit 3, nat_lit 13605119, nat_lit 0, nat_lit 1, nat_lit 2,
    nat_lit 4, nat_lit 6], [nat_lit 3, nat_lit 0, nat_lit 1, nat_lit 3]]]

@[expose] noncomputable def CNs2 : List (List Nat) :=
  [[nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 1, nat_lit 2, nat_lit 0, nat_lit 0, nat_lit 1,
    nat_lit 1], [nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0,
    nat_lit 0, nat_lit 1], [nat_lit 0, nat_lit 1, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0,
    nat_lit 0, nat_lit 0, nat_lit 0], [nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 1,
    nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0]]

@[expose] noncomputable def NP2 : List Nat :=
  [nat_lit 1, nat_lit 1, nat_lit 1, nat_lit 1]

end CertificateChecks.KernelCo1B.Bound17326.KC

#kss_co1dag CertificateChecks.KernelCo1B.Bound17326.DC CertificateChecks.KernelCo1B.Bound17326.kDagC

#kss_co1gt CertificateChecks.KernelCo1B.Bound17326.TT CertificateChecks.KernelCo1B.Bound17326.tArr 200

#kss_co1gt CertificateChecks.KernelCo1B.Bound17326.CT CertificateChecks.KernelCo1B.Bound17326.cArr 20000

end
