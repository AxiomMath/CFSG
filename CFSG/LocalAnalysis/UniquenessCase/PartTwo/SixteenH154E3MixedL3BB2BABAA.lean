module

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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

theorem s16h_e3_l3_sup_card_exp_of_commuting {X : Type} [Group X] [Finite X]
    {P Q : Subgroup X} (hPcard : Nat.card ↥P = 24) (hQcard : Nat.card ↥Q = 24)
    (hPexp : ∀ p ∈ P, p ^ 12 = 1) (hQexp : ∀ q ∈ Q, q ^ 12 = 1)
    (hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) (hdisj : P ⊓ Q = ⊥) :
    Nat.card ↥(P ⊔ Q) = 2 ^ 6 * 9 ∧ ∀ b ∈ P ⊔ Q, b ^ 24 = 1 := by
  classical
  let φ : ↥P × ↥Q →* X :=
    { toFun := fun x => (x.1 : X) * (x.2 : X)
      map_one' := by simp
      map_mul' := by
        intro x y
        have h := hcomm (y.1 : X) y.1.2 (x.2 : X) x.2.2
        show ((x.1 : X) * (y.1 : X)) * ((x.2 : X) * (y.2 : X)) =
          ((x.1 : X) * (x.2 : X)) * ((y.1 : X) * (y.2 : X))
        calc ((x.1 : X) * (y.1 : X)) * ((x.2 : X) * (y.2 : X))
            = (x.1 : X) * ((y.1 : X) * (x.2 : X)) * (y.2 : X) := by group
          _ = (x.1 : X) * ((x.2 : X) * (y.1 : X)) * (y.2 : X) := by rw [h]
          _ = ((x.1 : X) * (x.2 : X)) * ((y.1 : X) * (y.2 : X)) := by group }
  have hrange : φ.range = P ⊔ Q := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · refine sup_le ?_ ?_
      · intro p hp
        exact MonoidHom.mem_range.2 ⟨(⟨p, hp⟩, ⟨1, Q.one_mem⟩), by simp [φ]⟩
      · intro q hq
        exact MonoidHom.mem_range.2 ⟨(⟨1, P.one_mem⟩, ⟨q, hq⟩), by simp [φ]⟩
  have hker : φ.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro x hx
    have hx1 : (x.1 : X) * (x.2 : X) = 1 := MonoidHom.mem_ker.mp hx
    have hx1inv : (x.1 : X) = (x.2 : X)⁻¹ := by
      have h := eq_inv_of_mul_eq_one_right hx1
      rw [h, inv_inv]
    have hxP : (x.1 : X) ∈ P ⊓ Q := ⟨x.1.2, by rw [hx1inv]; exact Q.inv_mem x.2.2⟩
    rw [hdisj, mem_bot] at hxP
    have hx2 : (x.2 : X) = 1 := by
      rw [hxP, one_mul] at hx1
      exact hx1
    exact Prod.ext (Subtype.ext hxP) (Subtype.ext hx2)
  refine ⟨?_, ?_⟩
  · have h1 := Subgroup.card_ker_mul_card_range φ
    rw [hker, hrange, Subgroup.card_bot, Nat.card_prod, hPcard, hQcard] at h1
    norm_num at h1 ⊢
    exact h1
  · intro b hb
    have hbmem : b ∈ φ.range := by rw [hrange]; exact hb
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hbmem
    have hcommx : Commute (x.1 : X) (x.2 : X) := hcomm (x.1 : X) x.1.2 (x.2 : X) x.2.2
    have hp24 : (x.1 : X) ^ 24 = 1 := by
      have h := hPexp (x.1 : X) x.1.2
      rw [show (24 : ℕ) = 12 * 2 by norm_num, pow_mul, h, one_pow]
    have hq24 : (x.2 : X) ^ 24 = 1 := by
      have h := hQexp (x.2 : X) x.2.2
      rw [show (24 : ℕ) = 12 * 2 by norm_num, pow_mul, h, one_pow]
    calc b ^ 24 = ((x.1 : X) * (x.2 : X)) ^ 24 := by rw [← hx]; rfl
      _ = (x.1 : X) ^ 24 * (x.2 : X) ^ 24 := hcommx.mul_pow 24
      _ = 1 := by rw [hp24, hq24, one_mul]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
