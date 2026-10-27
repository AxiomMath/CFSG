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

namespace CFSG.Monster.B

theorem zmod_two_add_self {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (w : W) : w + w = 0 := by
  rw [← two_smul (ZMod 2) w, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem mul_self_eq_one_of_trivial_sub_quot {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (f : W →ₗ[ZMod 2] W) (U : Submodule (ZMod 2) W) (hU : ∀ u ∈ U, f u = u)
    (hQ : ∀ w, f w - w ∈ U) : f * f = 1 := by
  ext w
  have h1 : f (f w - w) = f w - w := hU _ (hQ w)
  rw [map_sub] at h1
  have h2 : f (f w) = f w - w + f w := by rw [← h1, sub_add_cancel]
  change f (f w) = w
  rw [h2, sub_add_eq_add_sub, zmod_two_add_self, zero_sub]
  have := zmod_two_add_self w
  exact (neg_eq_of_add_eq_zero_right this)

theorem eq_one_of_mul_self_eq_one_of_simple {G H : Type*} [Group G] [Group H] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (φ : G →* H) (hφ : ∀ g, φ g * φ g = 1) (g : G) :
    φ g = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    apply hab
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 h
    apply hinj
    have hx : ∀ x : G, (φ x)⁻¹ = φ x := fun x => inv_eq_of_mul_eq_one_right (hφ x)
    have hab' := hx (a * b)
    rw [map_mul, mul_inv_rev, hx a, hx b] at hab'
    rw [map_mul, map_mul]
    exact hab'.symm
  · exact (MonoidHom.mem_ker).1 (h ▸ Subgroup.mem_top g)

end CFSG.Monster.B
