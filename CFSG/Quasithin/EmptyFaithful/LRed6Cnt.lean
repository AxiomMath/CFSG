module

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

namespace CFSG.Quasithin

namespace LRed6

variable {G : Type*} [Group G]

theorem card_inf_ge [Finite G] {L R Γ : Subgroup G} (hLΓ : L ≤ Γ) (hRΓ : R ≤ Γ) {m : ℕ}
    (hm : L.relIndex Γ = 2 ^ m)
    (hR : 2 ^ padicValNat 2 (Nat.card Γ) ≤ 4 * Nat.card R) :
    2 ^ padicValNat 2 (Nat.card L) ≤ 4 * Nat.card ↥(R ⊓ L) := by
  have h1 : L.relIndex Γ * Nat.card ↥L = Nat.card ↥Γ := by
    have := Subgroup.relIndex_mul_card (H := L) (K := Γ)
    rwa [inf_eq_left.mpr hLΓ] at this
  have hLpos : 0 < Nat.card ↥L := Nat.card_pos
  have hv : padicValNat 2 (Nat.card ↥Γ) = m + padicValNat 2 (Nat.card ↥L) := by
    rw [← h1, hm]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [padicValNat.mul (by positivity) hLpos.ne', padicValNat.prime_pow]
  have h2 : (R ⊓ L).relIndex R ≤ 2 ^ m := by
    rw [inf_comm, Subgroup.inf_relIndex_right, ← hm]
    exact Subgroup.relIndex_le_of_le_right hRΓ (by
      rw [hm]; positivity)
  have h3 : (R ⊓ L).relIndex R * Nat.card ↥(R ⊓ L) = Nat.card ↥R := by
    have := Subgroup.relIndex_mul_card (H := R ⊓ L) (K := R)
    rwa [inf_eq_left.mpr (inf_le_left : R ⊓ L ≤ R)] at this
  rw [hv, pow_add] at hR
  have h4 : 2 ^ m * 2 ^ padicValNat 2 (Nat.card ↥L) ≤ 2 ^ m * (4 * Nat.card ↥(R ⊓ L)) := by
    calc 2 ^ m * 2 ^ padicValNat 2 (Nat.card ↥L) ≤ 4 * Nat.card ↥R := hR
      _ = 4 * ((R ⊓ L).relIndex R * Nat.card ↥(R ⊓ L)) := by rw [h3]
      _ ≤ 4 * (2 ^ m * Nat.card ↥(R ⊓ L)) := by
        gcongr
      _ = 2 ^ m * (4 * Nat.card ↥(R ⊓ L)) := by ring
  exact Nat.le_of_mul_le_mul_left h4 (by positivity)

end LRed6

end CFSG.Quasithin
