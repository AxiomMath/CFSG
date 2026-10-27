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

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

theorem orderOf_conj_fi {G : Type*} [Group G] (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  simpa [MulAut.conj_apply] using this

theorem exists_two_fixed_points {G : Type*} [Group G] {Ω : Type*} [Finite Ω] (rho : G →* Equiv.Perm Ω)
    {r : ℕ} (hr : r.Prime) (hr3 : 3 ≤ r) (hΩ : Nat.card Ω % r = 2) {s : G} (hs : s ^ r = 1) :
    ∃ ω₁ ω₂ : Ω, ω₁ ≠ ω₂ ∧ rho s ω₁ = ω₁ ∧ rho s ω₂ = ω₂ := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  let P : Subgroup (Equiv.Perm Ω) := Subgroup.zpowers (rho s)
  have hP : IsPGroup r P := by
    intro x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 x.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    have h1 : (rho s) ^ r = 1 := by rw [← map_pow, hs, map_one]
    rw [pow_one, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h1, one_zpow]
    rfl
  have hmod := hP.card_modEq_card_fixedPoints Ω
  have hf : Nat.card (MulAction.fixedPoints P Ω) % r = 2 := by
    have : Nat.card Ω % r = Nat.card (MulAction.fixedPoints P Ω) % r := hmod
    rw [← this]
    exact hΩ
  have hf2 : 2 ≤ Nat.card (MulAction.fixedPoints P Ω) := by
    by_contra hlt
    have hlt' : Nat.card (MulAction.fixedPoints P Ω) < 2 := by omega
    have : Nat.card (MulAction.fixedPoints P Ω) % r = Nat.card (MulAction.fixedPoints P Ω) :=
      Nat.mod_eq_of_lt (by omega)
    omega
  haveI : Finite (MulAction.fixedPoints P Ω) := inferInstance
  have hnt : Nontrivial (MulAction.fixedPoints P Ω) := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨⟨ω₁, h₁⟩, ⟨ω₂, h₂⟩, hne⟩ := exists_pair_ne (MulAction.fixedPoints P Ω)
  refine ⟨ω₁, ω₂, fun h => hne (Subtype.ext h), ?_, ?_⟩
  · exact MulAction.mem_fixedPoints.1 h₁ ⟨rho s, Subgroup.mem_zpowers _⟩
  · exact MulAction.mem_fixedPoints.1 h₂ ⟨rho s, Subgroup.mem_zpowers _⟩

theorem exists_conj_commute_of_fixed_points {G : Type*} [Group G] {Ω : Type*} [Finite Ω]
    (rho : G →* Equiv.Perm Ω)
    (h2 : ∀ b c d e : Ω, b ≠ c → d ≠ e → ∃ g : G, rho g b = d ∧ rho g c = e)
    {α β : Ω} (hαβ : α ≠ β) {T : Subgroup G}
    (hT : ∀ g : G, rho g α = α → rho g β = β → g ∈ T) (hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    {r : ℕ} (hr : r.Prime) (hr3 : 3 ≤ r) (hΩ : Nat.card Ω % r = 2) {s : G} (hs : s ^ r = 1)
    {z₀ : G} (hz₀ : z₀ ∈ T) :
    ∃ g : G, (g * z₀ * g⁻¹) * s = s * (g * z₀ * g⁻¹) := by
  obtain ⟨ω₁, ω₂, hne, hs1, hs2⟩ := exists_two_fixed_points rho hr hr3 hΩ hs
  obtain ⟨g, hg1, hg2⟩ := h2 α β ω₁ ω₂ hαβ hne
  have key : ∀ (a ω : Ω), rho g a = ω → rho s ω = ω → rho (g⁻¹ * s * g) a = a := by
    intro a ω h hω
    rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h, hω, map_inv]
    exact Equiv.Perm.inv_eq_iff_eq.2 h.symm
  have ht : g⁻¹ * s * g ∈ T := hT _ (key α ω₁ hg1 hs1) (key β ω₂ hg2 hs2)
  refine ⟨g, ?_⟩
  have hc := hTc z₀ hz₀ _ ht
  calc g * z₀ * g⁻¹ * s = g * (z₀ * (g⁻¹ * s * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * s * g) * z₀) * g⁻¹ := by rw [hc]
    _ = s * (g * z₀ * g⁻¹) := by group

end CFSG.LocalAnalysis.UniquenessCase.UCK
