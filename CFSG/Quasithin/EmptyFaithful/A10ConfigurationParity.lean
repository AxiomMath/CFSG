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

namespace CFSG.Quasithin.A10

variable {G : Type*} [Group G]

theorem isPGroup_zpowers_of_mul_self {u : G} (hu : u * u = 1) :
    IsPGroup 2 (Subgroup.zpowers u) := by
  intro g
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine ⟨1, ?_⟩
  apply Subtype.ext
  have h2 : u ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hu
  have h3 : (u ^ n) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simpa using congrArg (· ^ n) h2
  rw [pow_one, Subgroup.coe_pow, ← hn]
  exact h3

theorem exists_conj_mem_of_odd_index {C : Type*} [Group C] [Finite C] {H : Subgroup C}
    (hodd : ¬ 2 ∣ H.index) {u : C} (hu : u * u = 1) : ∃ c : C, c⁻¹ * u * c ∈ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZp := isPGroup_zpowers_of_mul_self hu
  have hnd : ¬ 2 ∣ Nat.card (C ⧸ H) := by rwa [← Subgroup.index_eq_card]
  obtain ⟨q, hq⟩ := hZp.nonempty_fixed_point_of_prime_not_dvd_card (C ⧸ H) hnd
  induction q using QuotientGroup.induction_on with
  | H c =>
    refine ⟨c, ?_⟩
    have h1 : (⟨u, Subgroup.mem_zpowers u⟩ : Subgroup.zpowers u) • (c : C ⧸ H) = (c : C ⧸ H) :=
      hq ⟨u, Subgroup.mem_zpowers u⟩
    have h2 : ((u * c : C) : C ⧸ H) = (c : C ⧸ H) := h1
    rw [QuotientGroup.eq] at h2
    have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
    have e : (u * c)⁻¹ * c = c⁻¹ * u * c := by rw [mul_inv_rev, hu']
    rw [e] at h2
    exact h2

theorem odd_index_centralizer_of_unique_fixed [Finite G] {M : Subgroup G} {z x : G}
    (hz2 : z * z = 1) (hzM : z ∈ M) (hcomm : x * z = z * x)
    (hfix : ∀ g : G, g⁻¹ * z * g ∈ M → g ∈ M) :
    ¬ 2 ∣ ((M ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf
      (Subgroup.centralizer ({x} : Set G))).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := Subgroup.centralizer ({x} : Set G) with hC
  set H : Subgroup C := (M ⊓ C).subgroupOf C with hH
  have hzC : z ∈ C := by
    rw [hC, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hcomm
  set z' : C := ⟨z, hzC⟩ with hz'
  have hz'2 : z' * z' = 1 := Subtype.ext hz2
  have hz'H : z' ∈ H := by
    rw [hH, Subgroup.mem_subgroupOf]
    exact ⟨hzM, hzC⟩
  have hZH : Subgroup.zpowers z' ≤ H := Subgroup.zpowers_le.2 hz'H
  have hZp := isPGroup_zpowers_of_mul_self hz'2
  have hmod := hZp.card_modEq_card_fixedPoints (C ⧸ H)
  have hmem1 : ∀ c : C, ((c : C) : C ⧸ H) = ((1 : C) : C ⧸ H) ↔ c ∈ H := by
    intro c
    rw [QuotientGroup.eq, mul_one]
    exact ⟨fun h => by simpa using H.inv_mem h, fun h => H.inv_mem h⟩
  have hfixcard : Nat.card (MulAction.fixedPoints (Subgroup.zpowers z') (C ⧸ H)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨?_⟩, ⟨⟨((1 : C) : C ⧸ H), ?_⟩⟩⟩
    · rintro ⟨q₁, hq₁⟩ ⟨q₂, hq₂⟩
      have key : ∀ q : C ⧸ H, (∀ g : Subgroup.zpowers z', g • q = q) →
          q = ((1 : C) : C ⧸ H) := by
        intro q hq
        induction q using QuotientGroup.induction_on with
        | H c =>
          have h1 : (⟨z', Subgroup.mem_zpowers z'⟩ : Subgroup.zpowers z') • (c : C ⧸ H) = c :=
            hq _
          have h2 : ((z' * c : C) : C ⧸ H) = (c : C ⧸ H) := h1
          rw [QuotientGroup.eq] at h2
          have hz'' : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz'2
          have e : (z' * c)⁻¹ * c = c⁻¹ * z' * c := by rw [mul_inv_rev, hz'']
          rw [e, hH, Subgroup.mem_subgroupOf] at h2
          have h3 : (c : G)⁻¹ * z * (c : G) ∈ M := h2.1
          have hcM : (c : G) ∈ M := hfix _ h3
          rw [hmem1, hH, Subgroup.mem_subgroupOf]
          exact ⟨hcM, c.2⟩
      exact Subtype.ext ((key q₁ hq₁).trans (key q₂ hq₂).symm)
    · intro g
      have hg : (g : C) ∈ H := hZH g.2
      show (g : C) • ((1 : C) : C ⧸ H) = ((1 : C) : C ⧸ H)
      have : (g : C) • ((1 : C) : C ⧸ H) = (((g : C) * 1 : C) : C ⧸ H) := rfl
      rw [this, mul_one, hmem1]
      exact hg
  rw [hfixcard] at hmod
  intro h2
  have h3 : H.index = Nat.card (C ⧸ H) := Subgroup.index_eq_card H
  rw [h3] at h2
  obtain ⟨k, hk⟩ := h2
  unfold Nat.ModEq at hmod
  omega

end CFSG.Quasithin.A10
