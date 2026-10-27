module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
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

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG CFSG.LocalCores

variable {E K : Type*} [Group E] [Group K]

theorem map_eq_top_of_isComponent [Finite E] (ρ : E →* K) (hρ : Function.Surjective ρ)
    (hker : Group.IsSolvable ρ.ker) (hKs : IsSimpleGroup K) {B : Subgroup E}
    (hB : CFSG.IsComponent B) : B.map ρ = ⊤ := by
  obtain ⟨hq, hsub⟩ := hB
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hKs (hsub.map hρ) with h | h
  · exfalso
    have hBk : B ≤ ρ.ker := (Subgroup.map_eq_bot_iff _).mp h
    have : Nontrivial B := isQuasisimple_nontrivial hq
    have : Group.IsPerfect B := hq.1
    have : Group.IsSolvable B :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hBk)
    exact Group.IsPerfect.not_isSolvable B this
  · exact h

theorem centralizer_eq_center_of_map_eq_top (ρ : E →* K) {B : Subgroup E} (hB : B.map ρ = ⊤)
    (hker : ρ.ker ≤ center E) : centralizer (B : Set E) = center E := by
  apply le_antisymm
  · intro x hx
    rw [mem_center_iff]
    intro e
    have he : ρ e ∈ B.map ρ := by rw [hB]; trivial
    obtain ⟨b, hb, hbe⟩ := mem_map.mp he
    have hk : b⁻¹ * e ∈ center E := hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hbe,
      inv_mul_cancel])
    have hxb := mem_centralizer_iff.mp hx b hb
    have hkx := mem_center_iff.mp hk x
    calc e * x = b * (b⁻¹ * e) * x := by group
      _ = b * (x * (b⁻¹ * e)) := by rw [mul_assoc, ← hkx]
      _ = b * x * (b⁻¹ * e) := by group
      _ = x * b * (b⁻¹ * e) := by rw [hxb]
      _ = x * e := by group
  · intro x hx
    rw [mem_centralizer_iff]
    intro b _
    exact mem_center_iff.mp hx b

theorem center_eq_ker_of_surjective (ρ : E →* K) (hρ : Function.Surjective ρ)
    (hK : center K = ⊥) (hker : ρ.ker ≤ center E) : center E = ρ.ker := by
  apply le_antisymm _ hker
  intro z hz
  rw [MonoidHom.mem_ker]
  have : ρ z ∈ center K := by
    rw [mem_center_iff]
    intro k
    obtain ⟨e, rfl⟩ := hρ k
    rw [← map_mul, ← map_mul, mem_center_iff.mp hz e]
  rw [hK, mem_bot] at this
  exact this

end CFSG.Sporadic.SmallOddCore
