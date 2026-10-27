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

namespace CFSG.Quasithin.H13.Seven

variable {G : Type*} [Group G]

theorem comm_three {E : Subgroup G} (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {a b c : G}
    (ha : a ∈ E) (hb : b ∈ E) (hc : c ∈ E) : a * b * c = c * b * a := by
  calc a * b * c = a * (b * c) := mul_assoc _ _ _
    _ = a * (c * b) := by rw [hE b hb c hc]
    _ = (a * c) * b := (mul_assoc _ _ _).symm
    _ = (c * a) * b := by rw [hE a ha c hc]
    _ = c * (a * b) := mul_assoc _ _ _
    _ = c * (b * a) := by rw [hE a ha b hb]
    _ = c * b * a := (mul_assoc _ _ _).symm

theorem kernel_map_of_inverting {E : Subgroup G} (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    {B g : G} (hB : ∀ n : ℕ, ∀ e ∈ E, B ^ n * e * (B ^ n)⁻¹ ∈ E)
    (hg : ∀ e ∈ E, g * e * g⁻¹ ∈ E) (hinv : g * B * g⁻¹ = B⁻¹) {e : G} (heE : e ∈ E)
    (he : (B ^ 3 * e * (B ^ 3)⁻¹) * (B * e * B⁻¹) * e = 1) :
    g * e * g⁻¹ ∈ E ∧
      (B ^ 3 * (g * e * g⁻¹) * (B ^ 3)⁻¹) * (B ^ 2 * (g * e * g⁻¹) * (B ^ 2)⁻¹) *
        (g * e * g⁻¹) = 1 := by
  set e' := g * e * g⁻¹ with he'
  have he'E : e' ∈ E := hg e heE
  refine ⟨he'E, ?_⟩
  set y := B ^ 3 * g with hy
  have hyB : y * B * y⁻¹ = B⁻¹ := by
    calc y * B * y⁻¹ = B ^ 3 * (g * B * g⁻¹) * (B ^ 3)⁻¹ := by rw [hy]; group
      _ = B⁻¹ := by rw [hinv]; group
  have hye : y * e * y⁻¹ = B ^ 3 * e' * (B ^ 3)⁻¹ := by rw [hy, he']; group
  have h1 := congrArg (MulAut.conj y) he
  simp only [map_mul, map_pow, map_inv, map_one, MulAut.conj_apply] at h1
  rw [hyB, hye] at h1
  have h2 : e' * (B ^ 2 * e' * (B ^ 2)⁻¹) * (B ^ 3 * e' * (B ^ 3)⁻¹) = 1 := by
    rw [← h1]; group
  have ha : B ^ 3 * e' * (B ^ 3)⁻¹ ∈ E := hB 3 e' he'E
  have hb : B ^ 2 * e' * (B ^ 2)⁻¹ ∈ E := hB 2 e' he'E
  rw [comm_three hE ha hb he'E]
  exact h2

theorem kernel_map_of_inverting' {E : Subgroup G} (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    {B g : G} (hB : ∀ n : ℕ, ∀ e ∈ E, B ^ n * e * (B ^ n)⁻¹ ∈ E)
    (hg' : ∀ e ∈ E, g⁻¹ * e * g ∈ E) (hinv : g⁻¹ * B * g = B⁻¹) {e : G} (heE : e ∈ E)
    (he : (B ^ 3 * e * (B ^ 3)⁻¹) * (B ^ 2 * e * (B ^ 2)⁻¹) * e = 1) :
    g⁻¹ * e * g ∈ E ∧
      (B ^ 3 * (g⁻¹ * e * g) * (B ^ 3)⁻¹) * (B * (g⁻¹ * e * g) * B⁻¹) * (g⁻¹ * e * g) = 1 := by
  set e' := g⁻¹ * e * g with he'
  have he'E : e' ∈ E := hg' e heE
  refine ⟨he'E, ?_⟩
  set y := B ^ 3 * g⁻¹ with hy
  have hyB : y * B * y⁻¹ = B⁻¹ := by
    calc y * B * y⁻¹ = B ^ 3 * (g⁻¹ * B * g) * (B ^ 3)⁻¹ := by rw [hy]; group
      _ = B⁻¹ := by rw [hinv]; group
  have hye : y * e * y⁻¹ = B ^ 3 * e' * (B ^ 3)⁻¹ := by rw [hy, he']; group
  have h1 := congrArg (MulAut.conj y) he
  simp only [map_mul, map_pow, map_inv, map_one, MulAut.conj_apply] at h1
  rw [hyB, hye] at h1
  have h2 : e' * (B * e' * B⁻¹) * (B ^ 3 * e' * (B ^ 3)⁻¹) = 1 := by
    rw [← h1]; group
  have ha : B ^ 3 * e' * (B ^ 3)⁻¹ ∈ E := hB 3 e' he'E
  have hb : B * e' * B⁻¹ ∈ E := by simpa using hB 1 e' he'E
  rw [comm_three hE ha hb he'E]
  exact h2

theorem ncard_kernel_eq [Finite G] {E : Subgroup G} (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    {B g : G} (hB : ∀ n : ℕ, ∀ e ∈ E, B ^ n * e * (B ^ n)⁻¹ ∈ E)
    (hg : ∀ e ∈ E, g * e * g⁻¹ ∈ E) (hg' : ∀ e ∈ E, g⁻¹ * e * g ∈ E)
    (hinv : g * B * g⁻¹ = B⁻¹) :
    {e : G | e ∈ E ∧ (B ^ 3 * e * (B ^ 3)⁻¹) * (B * e * B⁻¹) * e = 1}.ncard =
      {e : G | e ∈ E ∧ (B ^ 3 * e * (B ^ 3)⁻¹) * (B ^ 2 * e * (B ^ 2)⁻¹) * e = 1}.ncard := by
  have hinv' : g⁻¹ * B * g = B⁻¹ := by
    have h1 : B = g⁻¹ * B⁻¹ * g := by
      calc B = g⁻¹ * (g * B * g⁻¹) * g := by group
        _ = g⁻¹ * B⁻¹ * g := by rw [hinv]
    calc g⁻¹ * B * g = (g⁻¹ * B⁻¹ * g)⁻¹ := by group
      _ = B⁻¹ := by rw [← h1]
  apply le_antisymm
  · refine Set.ncard_le_ncard_of_injOn (fun e => g * e * g⁻¹) ?_ ?_ (Set.toFinite _)
    · rintro e ⟨heE, he⟩
      exact kernel_map_of_inverting hE hB hg hinv heE he
    · intro a _ b _ h
      simpa using h
  · refine Set.ncard_le_ncard_of_injOn (fun e => g⁻¹ * e * g) ?_ ?_ (Set.toFinite _)
    · rintro e ⟨heE, he⟩
      exact kernel_map_of_inverting' hE hB hg' hinv' heE he
    · intro a _ b _ h
      simpa using h

end CFSG.Quasithin.H13.Seven
