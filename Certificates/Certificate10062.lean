module

public import Certificates.Certificate3173Base
public import Certificates.Data.CFSGNative.Co1.Involutions
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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

open CFSG.Sporadic.SmallF2.Native

namespace CertificateChecks.Batch10062

open CFSG.Sporadic.SmallF2.Native

theorem validRows_idRows :
    CFSG.Sporadic.Co1.InvNative.validRows (idRows 24) = true := by
  simp only [CFSG.Sporadic.Co1.InvNative.validRows, Bool.and_eq_true, beq_iff_eq,
    Array.all_eq_true, decide_eq_true_eq]
  refine ⟨by simp [idRows], fun i hi => ?_⟩
  simp only [idRows, Array.getElem_ofFn]
  rw [Nat.one_shiftLeft]
  have : (i : ℕ) < 24 := by simpa [idRows] using hi
  calc 2 ^ i < 2 ^ 24 := Nat.pow_lt_pow_right (by norm_num) this
    _ = 16777216 := by norm_num

end CertificateChecks.Batch10062

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SmallF2.Native in
theorem certificate10062 :
    CFSG.Sporadic.Co1.InvNative.validRows (idRows 24) = true := CertificateChecks.Batch10062.validRows_idRows

end Certificates
