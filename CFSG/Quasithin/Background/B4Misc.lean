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

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

@[expose] def orbitOf (G : Subgroup (MulAut V)) (v : V) : Set V := {x | ∃ g ∈ G, g v = x}

@[expose] def IsTwoTransitiveOn (G : Subgroup (MulAut V)) (S : Set V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∀ c ∈ S, ∀ d ∈ S, c ≠ d → ∃ g ∈ G, g a = c ∧ g b = d

theorem orbit_eq_of_twoTransitive (hV : ∀ v : V, v ^ 2 = 1) (G : Subgroup (MulAut V)) (v : V)
    (hgen : Subgroup.closure (orbitOf G v) = ⊤)
    (U : Subgroup V) (hU : ∃ x ∈ U, ∃ y ∈ U, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y)
    (hUorb : ∀ u ∈ U, u ≠ 1 → u ∈ orbitOf G v)
    (h2 : IsTwoTransitiveOn G (orbitOf G v)) :
    ∀ x : V, x ≠ 1 → x ∈ orbitOf G v := by
  obtain ⟨x₀, hx₀, y₀, hy₀, hx1, hy1, hxy⟩ := hU
  have hprod : ∀ a ∈ orbitOf G v, ∀ b ∈ orbitOf G v, a ≠ b → a * b ∈ orbitOf G v := by
    intro a ha b hb hab
    have hx₀o : x₀ ∈ orbitOf G v := hUorb x₀ hx₀ hx1
    have hy₀o : y₀ ∈ orbitOf G v := hUorb y₀ hy₀ hy1
    obtain ⟨g, hg, hga, hgb⟩ := h2 x₀ hx₀o y₀ hy₀o hxy a ha b hb hab
    have hne : x₀ * y₀ ≠ 1 := by
      intro h
      apply hxy
      have h1 : x₀ = y₀⁻¹ := eq_inv_of_mul_eq_one_left h
      have h2' : y₀⁻¹ = y₀ := by
        have := hV y₀
        rw [pow_two] at this
        exact inv_eq_of_mul_eq_one_right this
      rw [h1, h2']
    have hmem : x₀ * y₀ ∈ orbitOf G v := hUorb _ (U.mul_mem hx₀ hy₀) hne
    obtain ⟨h, hh, hhv⟩ := hmem
    refine ⟨g * h, G.mul_mem hg hh, ?_⟩
    rw [MulAut.mul_apply, hhv, map_mul, hga, hgb]
  let W : Subgroup V :=
    { carrier := {x | x = 1 ∨ x ∈ orbitOf G v}
      one_mem' := Or.inl rfl
      mul_mem' := fun {a b} ha hb => by
        rcases ha with rfl | ha
        · rw [one_mul]; exact hb
        · rcases hb with rfl | hb
          · rw [mul_one]; exact Or.inr ha
          · by_cases hab : a = b
            · subst hab
              left
              have := hV a
              rwa [pow_two] at this
            · exact Or.inr (hprod a ha b hb hab)
      inv_mem' := fun {a} ha => by
        rcases ha with rfl | ha
        · left; exact inv_one
        · right
          have : a⁻¹ = a := by
            have := hV a
            rw [pow_two] at this
            exact inv_eq_of_mul_eq_one_right this
          rw [this]; exact ha }
  have hW : W = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    intro x hx
    exact Or.inr hx
  intro x hx1
  have : x ∈ W := by rw [hW]; trivial
  rcases this with h | h
  · exact absurd h hx1
  · exact h

end CFSG.Quasithin
