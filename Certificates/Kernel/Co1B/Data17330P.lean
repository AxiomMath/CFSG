module

public meta import Certificates.Kernel.Co1B.Gen17330P
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

namespace CertificateChecks.KernelCo1B.Bound17330.KP

@[expose] noncomputable def Sel : List (List Nat) :=
  [[nat_lit 1, nat_lit 0], [nat_lit 8, nat_lit 5], [nat_lit 1, nat_lit 3, nat_lit 2, nat_lit 4],
    [nat_lit 2, nat_lit 7, nat_lit 8, nat_lit 9, nat_lit 0, nat_lit 4], [nat_lit 28, nat_lit 10,
    nat_lit 29], [nat_lit 35, nat_lit 29, nat_lit 34, nat_lit 9, nat_lit 20, nat_lit 6, nat_lit 7,
    nat_lit 36, nat_lit 37], [nat_lit 45, nat_lit 35, nat_lit 48, nat_lit 16], [nat_lit 33,
    nat_lit 30, nat_lit 21, nat_lit 17], [nat_lit 32, nat_lit 9, nat_lit 17, nat_lit 23,
    nat_lit 26], [nat_lit 30, nat_lit 5, nat_lit 12, nat_lit 11], [nat_lit 18, nat_lit 27,
    nat_lit 25, nat_lit 17, nat_lit 20, nat_lit 24], [nat_lit 133, nat_lit 134], [nat_lit 29,
    nat_lit 20, nat_lit 23], [nat_lit 80, nat_lit 36, nat_lit 1, nat_lit 28, nat_lit 0, nat_lit 19,
    nat_lit 31, nat_lit 81]]

@[expose] noncomputable def CFs : List (List (List Nat)) :=
  [[[nat_lit 2, nat_lit 0, nat_lit 0, nat_lit 1, nat_lit 2], [nat_lit 3, nat_lit 0, nat_lit 0,
    nat_lit 1]], [[nat_lit 0, nat_lit 3142828, nat_lit 0, nat_lit 2], [nat_lit 3, nat_lit 7844110,
    nat_lit 2]], [[nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 1, nat_lit 2], [nat_lit 2,
    nat_lit 7844110, nat_lit 1], [nat_lit 3, nat_lit 7844110, nat_lit 0], [nat_lit 3,
    nat_lit 7844110, nat_lit 0, nat_lit 1]], [[nat_lit 2, nat_lit 7844110, nat_lit 0], [nat_lit 2,
    nat_lit 4471606, nat_lit 1], [nat_lit 2, nat_lit 14209169, nat_lit 0], [nat_lit 3,
    nat_lit 14209169, nat_lit 2], [nat_lit 3, nat_lit 0, nat_lit 0, nat_lit 1], [nat_lit 3,
    nat_lit 7844110, nat_lit 2]], [[nat_lit 2, nat_lit 8426803, nat_lit 0, nat_lit 2], [nat_lit 2,
    nat_lit 4471606, nat_lit 1], [nat_lit 2, nat_lit 10201097, nat_lit 1]], [[nat_lit 2,
    nat_lit 2038621, nat_lit 0, nat_lit 1], [nat_lit 2, nat_lit 9300350, nat_lit 1], [nat_lit 2,
    nat_lit 3142828, nat_lit 0, nat_lit 2], [nat_lit 3, nat_lit 4471606, nat_lit 0], [nat_lit 3,
    nat_lit 14209169, nat_lit 0, nat_lit 2], [nat_lit 3, nat_lit 7844110, nat_lit 0, nat_lit 2],
    [nat_lit 3, nat_lit 7844110, nat_lit 1, nat_lit 2], [nat_lit 3, nat_lit 11493791, nat_lit 0,
    nat_lit 2], [nat_lit 3, nat_lit 10283943, nat_lit 1, nat_lit 2]], [[nat_lit 2, nat_lit 2893749,
    nat_lit 0, nat_lit 1], [nat_lit 2, nat_lit 463880, nat_lit 0], [nat_lit 2, nat_lit 15446881,
    nat_lit 0, nat_lit 1], [nat_lit 3, nat_lit 14209169, nat_lit 0]], [[nat_lit 2,
    nat_lit 12146298, nat_lit 0, nat_lit 2], [nat_lit 2, nat_lit 463880, nat_lit 0], [nat_lit 2,
    nat_lit 14209169, nat_lit 1, nat_lit 2], [nat_lit 3, nat_lit 14209169, nat_lit 1]],
    [[nat_lit 2, nat_lit 10539895, nat_lit 1, nat_lit 2], [nat_lit 2, nat_lit 4471606, nat_lit 0],
    [nat_lit 2, nat_lit 14209169, nat_lit 0, nat_lit 2], [nat_lit 2, nat_lit 9300350, nat_lit 2],
    [nat_lit 3, nat_lit 6680394, nat_lit 0]], [[nat_lit 2, nat_lit 9338881, nat_lit 2], [nat_lit 2,
    nat_lit 7844110, nat_lit 2], [nat_lit 2, nat_lit 14209169, nat_lit 2], [nat_lit 2,
    nat_lit 14209169, nat_lit 1]], [[nat_lit 2, nat_lit 15472903, nat_lit 0, nat_lit 1],
    [nat_lit 2, nat_lit 11444268, nat_lit 2], [nat_lit 2, nat_lit 7477158, nat_lit 0, nat_lit 1],
    [nat_lit 2, nat_lit 15472903, nat_lit 0], [nat_lit 3, nat_lit 15472903, nat_lit 0, nat_lit 2],
    [nat_lit 3, nat_lit 7477158, nat_lit 1]], [[nat_lit 2, nat_lit 3613653, nat_lit 0, nat_lit 1,
    nat_lit 2], [nat_lit 2, nat_lit 12384864, nat_lit 2]], [[nat_lit 2, nat_lit 6765246,
    nat_lit 1], [nat_lit 2, nat_lit 463880, nat_lit 1, nat_lit 2], [nat_lit 2, nat_lit 7477158,
    nat_lit 1]], [[nat_lit 2, nat_lit 13523507, nat_lit 0], [nat_lit 2, nat_lit 7810584,
    nat_lit 0], [nat_lit 3, nat_lit 0, nat_lit 0, nat_lit 1, nat_lit 2], [nat_lit 3,
    nat_lit 13937945, nat_lit 2], [nat_lit 3, nat_lit 0, nat_lit 0, nat_lit 1], [nat_lit 3,
    nat_lit 463880, nat_lit 2], [nat_lit 3, nat_lit 11444268, nat_lit 2], [nat_lit 3,
    nat_lit 12532159, nat_lit 0]]]

@[expose] noncomputable def CNs : List (List Nat) :=
  [[nat_lit 3409, nat_lit 3385, nat_lit 3374, nat_lit 3385, nat_lit 3453, nat_lit 3318,
    nat_lit 3495, nat_lit 3344, nat_lit 3455], [nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 2,
    nat_lit 2, nat_lit 0, nat_lit 4, nat_lit 2, nat_lit 1], [nat_lit 2, nat_lit 3, nat_lit 1,
    nat_lit 1, nat_lit 2, nat_lit 0, nat_lit 0, nat_lit 4, nat_lit 3], [nat_lit 1, nat_lit 0,
    nat_lit 0, nat_lit 0, nat_lit 1, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0], [nat_lit 0,
    nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 1],
    [nat_lit 1, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 1,
    nat_lit 0], [nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0,
    nat_lit 1, nat_lit 0], [nat_lit 0, nat_lit 0, nat_lit 1, nat_lit 0, nat_lit 0, nat_lit 0,
    nat_lit 0, nat_lit 0, nat_lit 0], [nat_lit 1, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0,
    nat_lit 1, nat_lit 0, nat_lit 0, nat_lit 0], [nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0,
    nat_lit 0, nat_lit 0, nat_lit 1, nat_lit 0, nat_lit 0], [nat_lit 1, nat_lit 0, nat_lit 0,
    nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0], [nat_lit 0, nat_lit 0,
    nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 1, nat_lit 0, nat_lit 0, nat_lit 0], [nat_lit 0,
    nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 1, nat_lit 0, nat_lit 0, nat_lit 0],
    [nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 1,
    nat_lit 0]]

@[expose] noncomputable def NP : List Nat :=
  [nat_lit 2, nat_lit 1, nat_lit 1, nat_lit 2, nat_lit 2, nat_lit 1, nat_lit 1, nat_lit 1,
    nat_lit 2, nat_lit 1, nat_lit 2, nat_lit 1, nat_lit 1, nat_lit 1]

@[expose] noncomputable def Sel2 : List (List Nat) :=
  [[nat_lit 12, nat_lit 13, nat_lit 8, nat_lit 1], [nat_lit 40, nat_lit 48, nat_lit 17, nat_lit 41,
    nat_lit 14, nat_lit 12, nat_lit 13, nat_lit 7, nat_lit 33, nat_lit 16, nat_lit 30, nat_lit 49],
    [nat_lit 9, nat_lit 20, nat_lit 16, nat_lit 22, nat_lit 23, nat_lit 24]]

@[expose] noncomputable def CFs2 : List (List (List Nat)) :=
  [[[nat_lit 2, nat_lit 0, nat_lit 1, nat_lit 8], [nat_lit 2, nat_lit 0, nat_lit 3, nat_lit 6],
    [nat_lit 2, nat_lit 0, nat_lit 0, nat_lit 9], [nat_lit 3, nat_lit 0, nat_lit 0, nat_lit 2]],
    [[nat_lit 2, nat_lit 0, nat_lit 8, nat_lit 10], [nat_lit 2, nat_lit 15759851, nat_lit 2,
    nat_lit 3], [nat_lit 3, nat_lit 0, nat_lit 1, nat_lit 11], [nat_lit 2, nat_lit 0, nat_lit 9,
    nat_lit 10], [nat_lit 3, nat_lit 0, nat_lit 1, nat_lit 6], [nat_lit 3, nat_lit 0, nat_lit 1,
    nat_lit 3], [nat_lit 3, nat_lit 0, nat_lit 1, nat_lit 4], [nat_lit 3, nat_lit 0, nat_lit 0,
    nat_lit 8], [nat_lit 3, nat_lit 0, nat_lit 5, nat_lit 6], [nat_lit 3, nat_lit 0, nat_lit 1,
    nat_lit 9], [nat_lit 3, nat_lit 0, nat_lit 4, nat_lit 5], [nat_lit 3, nat_lit 5253729,
    nat_lit 0, nat_lit 10]], [[nat_lit 2, nat_lit 0, nat_lit 0, nat_lit 10], [nat_lit 2, nat_lit 0,
    nat_lit 6, nat_lit 7], [nat_lit 3, nat_lit 0, nat_lit 1, nat_lit 11], [nat_lit 2,
    nat_lit 7393384, nat_lit 1], [nat_lit 3, nat_lit 5686435, nat_lit 0, nat_lit 10], [nat_lit 3,
    nat_lit 5686435, nat_lit 0, nat_lit 11]]]

@[expose] noncomputable def CNs2 : List (List Nat) :=
  [[nat_lit 2, nat_lit 1, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0,
    nat_lit 0], [nat_lit 0, nat_lit 1, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0,
    nat_lit 0, nat_lit 2], [nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 0, nat_lit 1, nat_lit 0,
    nat_lit 0, nat_lit 0, nat_lit 0]]

@[expose] noncomputable def NP2 : List Nat :=
  [nat_lit 2, nat_lit 2, nat_lit 2]

end CertificateChecks.KernelCo1B.Bound17330.KP

end
