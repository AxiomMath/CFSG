module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23Alt7Inputs
import Certificates.Kernel.Misc.A7Cnt
import CFSG.Certificates.Kernel.Misc.A7CntSound
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

open CertificateChecks.KernelA7Cnt CFSG.KC.A7Cnt in
open CFSG CFSG.Quasithin CFSG.Quasithin.H13 Equiv MulAction in
open scoped Pointwise in
theorem certificate7055 :
    ((Finset.univ.filter fun σ : Perm (Fin 7) => Perm.sign σ = 1 ∧ Pres56 σ).card = 120)
    ∧ ((Finset.univ.filter fun σ : Perm (Fin 7) =>
       Perm.sign σ = 1 ∧ ∀ i : Fin 7, ((σ i).val < 4 ↔ i.val < 4)).card = 72)
    ∧ ((Finset.univ.filter fun σ : Perm (Fin 7) => Perm.sign σ = 1 ∧ σ 4 = 4).card = 360)
    ∧ ((Finset.univ.filter fun σ : Perm (Fin 7) =>
       Perm.sign σ = 1 ∧ σ 4 = 4 ∧ σ ^ 5 = 1).card = 145)
    ∧ ((Finset.univ.filter fun σ : Perm (Fin 7) => Perm.sign σ = 1 ∧ σ ^ 35 = 1).card = 1225)
    ∧ ((Finset.univ.filter fun σ : Perm (Fin 7) => Perm.sign σ = 1 ∧ σ ^ 7 = 1).card = 721)
    ∧ (∀ x : Perm (Fin 7), Perm.sign x = 1 → x ≠ 1 →
       x * x = 1 →
         (Finset.univ.filter fun y : Perm (Fin 7) => Perm.sign y = 1 ∧ x * y = y * x).card = 24) :=
  ⟨k1_eq.symm.trans (Nat.eq_of_beq_eq_true k1_120),
    k2_eq.symm.trans (Nat.eq_of_beq_eq_true k2_72),
    k3_eq.symm.trans (Nat.eq_of_beq_eq_true k3_360),
    k4_eq.symm.trans (Nat.eq_of_beq_eq_true k4_145),
    k5_eq.symm.trans (Nat.eq_of_beq_eq_true k5_1225),
    k6_eq.symm.trans (Nat.eq_of_beq_eq_true k6_721),
    cent_card invK_true (Nat.eq_of_beq_eq_true centK_24)⟩

end Certificates
