module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Tactic.NormNum.GCD
import CFSG.Certificates.Kernel.PermCent.FastDecide
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

public section

namespace CertificateChecks.Batch23600

open Equiv

private def Cond (σ q : Perm (Fin 6)) : Prop :=
  σ * σ = 1 → Perm.sign σ = -1 → Perm.sign q = 1 → q ^ 4 = 1 → q ^ 2 ≠ 1 → σ * q = q * σ →
    (∃ i j : Fin 6, i ≠ j ∧ σ = swap i j) ∨ ∃ i j : Fin 6, i ≠ j ∧ σ * q ^ 2 = swap i j

private instance (σ q : Perm (Fin 6)) : Decidable (Cond σ q) := by
  unfold Cond
  infer_instance

open scoped CFSG.Certificates.Kernel.PkCV.FastDecide

private def CondQ (σ q : Perm (Fin 6)) : Prop :=
  σ * q = q * σ → q ^ 4 = 1 → q ^ 2 ≠ 1 → Perm.sign q = 1 →
    ∃ i j : Fin 6, i ≠ j ∧ σ * q ^ 2 = swap i j

private instance (σ q : Perm (Fin 6)) : Decidable (CondQ σ q) := by
  unfold CondQ
  infer_instance

private def CondS (σ : Perm (Fin 6)) : Prop :=
  σ * σ = 1 → Perm.sign σ = -1 → (∃ i j : Fin 6, i ≠ j ∧ σ = swap i j) ∨ ∀ q, CondQ σ q

private noncomputable instance (σ : Perm (Fin 6)) : Decidable (CondS σ) := by
  unfold CondS
  infer_instance

private theorem odd_involution_swap_aux : ∀ σ : Perm (Fin 6), CondS σ := by
  decide +kernel

private theorem odd_involution_swap_0 : ∀ σ q : Perm (Fin 6), Cond σ q := by
  intro σ q
  unfold Cond
  intro h1 h2 h3 h4 h5 h6
  rcases odd_involution_swap_aux σ h1 h2 with h | h
  · exact Or.inl h
  · exact Or.inr (h q h6 h4 h5 h3)

end CertificateChecks.Batch23600

namespace Certificates

open CertificateChecks

theorem certificate23600 : ∀ σ q : Equiv.Perm (Fin 6), σ * σ = 1 → Equiv.Perm.sign σ = -1 →
    Equiv.Perm.sign q = 1 → q ^ 4 = 1 → q ^ 2 ≠ 1 → σ * q = q * σ →
      (∃ i j : Fin 6, i ≠ j ∧ σ = Equiv.swap i j) ∨
        ∃ i j : Fin 6, i ≠ j ∧ σ * q ^ 2 = Equiv.swap i j :=
  fun σ q h1 h2 h3 h4 h5 h6 => CertificateChecks.Batch23600.odd_involution_swap_0 σ q h1 h2 h3 h4 h5 h6

end Certificates
