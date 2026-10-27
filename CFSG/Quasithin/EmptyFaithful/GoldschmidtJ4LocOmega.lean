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

namespace CFSG.Quasithin.J4Loc

variable {G : Type*} [Group G]

@[expose] def omegaZ (N : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ N ∧ (∀ y ∈ N, x * y = y * x) ∧ x * x = 1}
  mul_mem' := by
    rintro a b ⟨haN, hac, has⟩ ⟨hbN, hbc, hbs⟩
    refine ⟨N.mul_mem haN hbN, fun y hy => ?_, ?_⟩
    · rw [mul_assoc, hbc y hy, ← mul_assoc, hac y hy, mul_assoc]
    · have hab : a * b = b * a := hac b hbN
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [← hab]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [has, hbs, one_mul]
  one_mem' := ⟨N.one_mem, fun y _ => by simp, by simp⟩
  inv_mem' := by
    rintro a ⟨haN, hac, has⟩
    refine ⟨N.inv_mem haN, fun y hy => ?_, ?_⟩
    · have h1 := hac y hy
      calc a⁻¹ * y = a⁻¹ * (y * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * y) * a⁻¹ := by rw [← h1]
        _ = y * a⁻¹ := by group
    · have : a * a = 1 := has
      calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
        _ = 1 := by rw [this]; simp

theorem mem_omegaZ {N : Subgroup G} {x : G} :
    x ∈ omegaZ N ↔ x ∈ N ∧ (∀ y ∈ N, x * y = y * x) ∧ x * x = 1 := Iff.rfl

theorem omegaZ_le (N : Subgroup G) : omegaZ N ≤ N := fun _ hx => hx.1

theorem omegaZ_conj {N : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (N : Set G)) {x : G}
    (hx : x ∈ omegaZ N) : g * x * g⁻¹ ∈ omegaZ N := by
  obtain ⟨hxN, hxc, hxs⟩ := hx
  have h1 : g * x * g⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.1 hg x).1 hxN
  refine ⟨h1, fun y hy => ?_, ?_⟩
  · have hy' : g⁻¹ * y * g ∈ N := by
      have := Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * y * g)
      have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      rw [e] at this
      exact this.2 hy
    have := hxc _ hy'
    calc g * x * g⁻¹ * y = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by rw [this]
      _ = y * (g * x * g⁻¹) := by group
  · calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hxs]; group

theorem omegaZ_ne_bot [Finite G] {N : Subgroup G} (hN : IsPGroup 2 N) (hne : N ≠ ⊥) :
    omegaZ N ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).2 hne
  have : Nontrivial (Subgroup.center N) := hN.center_nontrivial
  have hZ : IsPGroup 2 (Subgroup.center N) := hN.to_subgroup _
  obtain ⟨n, hn, hcard⟩ := (hZ.nontrivial_iff_card).1 inferInstance
  have h2 : 2 ∣ Nat.card (Subgroup.center N) := by
    rw [hcard]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    omega
  have hzs : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz, sq] at this
    exact this
  refine (Subgroup.ne_bot_iff_exists_ne_one).2 ⟨⟨((z : N) : G), ?_⟩, ?_⟩
  · refine ⟨(z : N).2, fun y hy => ?_, ?_⟩
    · have := Subgroup.mem_center_iff.1 z.2 ⟨y, hy⟩
      exact (congrArg Subtype.val this).symm
    · have := congrArg (fun w : Subgroup.center N => (((w : N) : G))) hzs
      simpa using this
  · intro h
    apply hz1
    have h' : (((z : N) : G)) = 1 := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')

end CFSG.Quasithin.J4Loc
