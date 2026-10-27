module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3Groups
import Certificates.Kernel.Sporadic.J3C.Glue
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

namespace Certificates

open CertificateChecks.KernelSpor.J3CGlue in
open CFSG CFSG.ClassicalInvolution in
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.ClassicalInvolution.J3Data in
theorem certificate9309 : (∀ h < 2, isInvA 20520 abArr[h]! abInv[h]! = true)
    ∧ (rawChainOK 20520 (sStrong.extract 0 4) sStrong sBase sDeriv 4 = true ∧
      rawOrbitSizes 20520 sStrong sBase = [128, 1, 1])
    ∧ (Nat.card J3Groups.K = 1920 ∧ (∀ g ∈ J3Groups.K, g * J3Groups.pa = J3Groups.pa * g) ∧
      ∀ g ∈ J3Groups.P, g * J3Groups.pa = J3Groups.pa * g → g ∈ J3Groups.K)
    ∧ (J3Groups.K ≤ Subgroup.normalizer (J3Groups.U : Set (Equiv.Perm (Fin 20520))) ∧
      Nat.card J3Groups.U = 32 ∧
      ∀ g ∈ J3Groups.K, (∀ u ∈ J3Groups.U, g * u = u * g) → g ∈ J3Groups.U)
    ∧ (∀ s ∈ J3Groups.S, orderOf s = 2 → ∃ c ∈ J3Groups.P, s = c * J3Groups.pa * c⁻¹) :=
  ⟨ab_ok, sChain_ok, centK, uFacts, coverS⟩

end Certificates
