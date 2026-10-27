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
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.Quasithin.G112A2

section Field4

variable {K : Type} [Field K]

theorem g112A2Seven_mem_cases [Finite K] (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) (c : K) : c = 0 ∨ c = 1 ∨ c = ω ∨ c = ω ^ 2 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have h4 : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hc4 : c ^ 4 = c := by
    have := FiniteField.pow_card c
    rw [h4] at this
    exact this
  have key : c * (c - 1) * (c - ω) * (c - ω ^ 2) = 0 := by
    linear_combination hc4 + (c ^ 2 - c ^ 3 + (ω - 1) * (c ^ 2 - c)) * hω
  rcases mul_eq_zero.mp key with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (sub_eq_zero.mp h))
    · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h)))
  · exact Or.inr (Or.inr (Or.inr (sub_eq_zero.mp h)))

theorem g112A2Seven_exists_omega [Finite K] (hK : Nat.card K = 4) :
    ∃ ω : K, ω ^ 2 + ω + 1 = 0 ∧ ω ≠ 0 ∧ ω ≠ 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have h4 : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact hK
  obtain ⟨c, hc0, hc1⟩ : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hle : Fintype.card K ≤ Fintype.card (Fin 2) := by
      apply Fintype.card_le_of_surjective (fun i : Fin 2 => if (i : ℕ) = 0 then (0 : K) else 1)
      intro x
      by_cases hx : x = 0
      · exact ⟨0, by simp [hx]⟩
      · exact ⟨1, by simp [hcon x hx]⟩
    rw [h4, Fintype.card_fin] at hle
    omega
  have hc4 : c ^ 4 = c := by
    have := FiniteField.pow_card c
    rw [h4] at this
    exact this
  have hc3 : c ^ 3 = 1 := by
    have h : c * (c ^ 3 - 1) = 0 := by linear_combination hc4
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hc0
    · linear_combination h
  refine ⟨c, ?_, hc0, hc1⟩
  have h : (c - 1) * (c ^ 2 + c + 1) = 0 := by linear_combination hc3
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) hc1
  · linear_combination h

theorem g112A2Seven_sq_surj [Finite K] (h2 : (2 : K) = 0) :
    Function.Surjective (fun μ : K => μ * μ) := by
  apply Finite.surjective_of_injective
  intro μ ν h
  have h0 : μ * μ = ν * ν := h
  have h' : (μ - ν) * (μ - ν) = 0 := by
    linear_combination h0 + (ν * ν - μ * ν) * h2
  exact sub_eq_zero.mp (mul_self_eq_zero.mp h')

theorem g112A2Seven_finrank_gf4 [Algebra (ZMod 2) K] [Finite K] (hK : Nat.card K = 4) :
    Module.finrank (ZMod 2) K = 2 := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)
  rw [Nat.card_zmod, hK] at h
  have h' : (2 : ℕ) ^ Module.finrank (ZMod 2) K = 2 ^ 2 := by
    rw [← h]
    norm_num
  exact Nat.pow_right_injective (le_refl 2) h'

end Field4

section Scalars

variable {K : Type} [Field K] [Algebra (ZMod 2) K]

@[expose] def g112A2SevenSmul {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Module K M]
    [IsScalarTower (ZMod 2) K M] (c : K) : M →ₗ[ZMod 2] M :=
  (LinearMap.lsmul K M c).restrictScalars (ZMod 2)

theorem g112A2SevenSmul_apply {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Module K M]
    [IsScalarTower (ZMod 2) K M] (c : K) (X : M) :
    g112A2SevenSmul c X = c • X := rfl

theorem g112A2Seven_finrank_range_ge_four_of_semilinear {M : Type} [AddCommGroup M]
    [Module (ZMod 2) M] [Module K M] [IsScalarTower (ZMod 2) K M] [FiniteDimensional (ZMod 2) M]
    {ω : K} (hne : ω ≠ ω ^ 2) (t : M ≃ₗ[ZMod 2] M) (hs : ∀ X, t (ω • X) = ω ^ 2 • t X)
    (hdim : Module.finrank (ZMod 2) M = 8) :
    4 ≤ Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) := by
  have hfix : ∀ b ∈ LinearMap.ker (t.toLinearMap - LinearMap.id), t b = b := by
    intro b hb
    have h1 := LinearMap.mem_ker.mp hb
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at h1
    exact sub_eq_zero.mp h1
  let Φ : (LinearMap.ker (t.toLinearMap - LinearMap.id) × LinearMap.ker (t.toLinearMap - LinearMap.id))
      →ₗ[ZMod 2] M :=
    LinearMap.coprod (LinearMap.ker (t.toLinearMap - LinearMap.id)).subtype
      ((g112A2SevenSmul ω).comp (LinearMap.ker (t.toLinearMap - LinearMap.id)).subtype)
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ h
    have h0 : a + ω • b = 0 := by simpa [Φ, g112A2SevenSmul_apply] using h
    have h1 : t (a + ω • b) = 0 := by rw [h0, map_zero]
    rw [map_add, hs, hfix a ha, hfix b hb] at h1
    have h2 : (ω - ω ^ 2) • b = 0 := by linear_combination (norm := module) h0 - h1
    have hb0 : b = 0 := (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)
    have ha0 : a = 0 := by
      rw [hb0, smul_zero, add_zero] at h0
      exact h0
    subst hb0
    subst ha0
    rfl
  have hcard : Module.finrank (ZMod 2) (LinearMap.ker (t.toLinearMap - LinearMap.id) ×
      LinearMap.ker (t.toLinearMap - LinearMap.id)) ≤ 8 := by
    rw [← hdim]
    exact LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod] at hcard
  have hrn := LinearMap.finrank_range_add_finrank_ker (t.toLinearMap - LinearMap.id)
  rw [hdim] at hrn
  omega

end Scalars

section Pairs

theorem g112A2Seven_exists_both_ne {M : Type} [AddCommGroup M] {E : Type} [AddZeroClass E]
    (a g : M → E) (ha : ∀ x y, a (x + y) = a x + a y) (hg : ∀ x y, g (x + y) = g x + g y)
    (h1 : ∃ x, a x ≠ 0) (h2 : ∃ y, g y ≠ 0) : ∃ x, a x ≠ 0 ∧ g x ≠ 0 := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  by_cases hgx : g x = 0
  · by_cases hay : a y = 0
    · refine ⟨x + y, ?_, ?_⟩
      · rw [ha, hay, add_zero]
        exact hx
      · rw [hg, hgx, zero_add]
        exact hy
    · exact ⟨y, hay, hy⟩
  · exact ⟨x, hx, hgx⟩

end Pairs

end CFSG.Quasithin.G112A2
