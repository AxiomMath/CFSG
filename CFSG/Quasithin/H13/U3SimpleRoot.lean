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

namespace CFSG.Quasithin.H13.U3

open Subgroup

theorem simple_transitive_root_proper_overgroups {G Ω : Type*} [Group G] [IsSimpleGroup G]
    [MulAction G Ω] (α : Ω) {U : Subgroup G} (hU1 : U ≠ ⊥)
    (hUα : U ≤ MulAction.stabilizer G α)
    (hUn : (U.subgroupOf (MulAction.stabilizer G α)).Normal)
    (hUt : ∀ β γ : Ω, β ≠ α → γ ≠ α → ∃ u ∈ U, u • β = γ) {M : Subgroup G} (hM : M < ⊤)
    (hUM : U ≤ M) : M ≤ MulAction.stabilizer G α := by
  have hN : MulAction.stabilizer G α ≤ normalizer (U : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hUα).1 hUn
  by_contra hMα
  obtain ⟨m, hmM, hmα⟩ := IsConcreteLE.not_le_iff_exists.1 hMα
  rw [MulAction.mem_stabilizer_iff] at hmα
  have htrans : ∀ β : Ω, ∃ x ∈ M, x • α = β := by
    intro β
    by_cases hβ : β = α
    · exact ⟨1, M.one_mem, by rw [one_smul, hβ]⟩
    · obtain ⟨u, hu, huβ⟩ := hUt (m • α) β hmα hβ
      exact ⟨u * m, M.mul_mem (hUM hu) hmM, by rw [mul_smul, huβ]⟩
  have hconj : ∀ u ∈ U, ∀ g : G, g * u * g⁻¹ ∈ M := by
    intro u hu g
    obtain ⟨x, hxM, hxα⟩ := htrans (g • α)
    have hs : x⁻¹ * g ∈ MulAction.stabilizer G α := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, ← hxα, inv_smul_smul]
    have h1 : (x⁻¹ * g) * u * (x⁻¹ * g)⁻¹ ∈ U := (mem_normalizer_iff.1 (hN hs) u).1 hu
    have h2 : g * u * g⁻¹ = x * ((x⁻¹ * g) * u * (x⁻¹ * g)⁻¹) * x⁻¹ := by group
    rw [h2]
    exact M.mul_mem (M.mul_mem hxM (hUM h1)) (M.inv_mem hxM)
  have hcore : U ≤ M.normalCore := fun u hu g => hconj u hu g
  have hcore1 : M.normalCore ≠ ⊥ := fun h => hU1 (le_bot_iff.1 (h ▸ hcore))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M.normalCore with h | h
  · exact hcore1 h
  · exact hM.ne (top_le_iff.1 (h ▸ M.normalCore_le))

end CFSG.Quasithin.H13.U3
