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

namespace CFSG.Quasithin.H13.F431.U42

variable {K : Type*} [Group K]

theorem conj_eq_inv_of_fixedPointFree (O : Subgroup K) [hO : O.Normal] [Finite O] (c : K)
    (hc : c * c = 1) (hfix : ∀ o ∈ O, o * c = c * o → o = 1) (o : K) (ho : o ∈ O) :
    c * o * c⁻¹ = o⁻¹ := by
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  let f : O → O := fun x => ⟨(x : K)⁻¹ * (c * x * c⁻¹), O.mul_mem (O.inv_mem x.2)
    (hO.conj_mem x x.2 c)⟩
  have hinj : Function.Injective f := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have h1 : x⁻¹ * (c * x * c⁻¹) = y⁻¹ * (c * y * c⁻¹) := congrArg Subtype.val hxy
    have h3 : x⁻¹ * c * x = y⁻¹ * c * y := by
      have h1' : x⁻¹ * (c * x * c⁻¹) * c = y⁻¹ * (c * y * c⁻¹) * c := by rw [h1]
      simpa [mul_assoc] using h1'
    have h2 : y * x⁻¹ * c = c * (y * x⁻¹) := by
      calc y * x⁻¹ * c = y * (x⁻¹ * c * x) * x⁻¹ := by group
        _ = y * (y⁻¹ * c * y) * x⁻¹ := by rw [h3]
        _ = c * (y * x⁻¹) := by group
    have h4 := hfix _ (O.mul_mem hy (O.inv_mem hx)) h2
    exact Subtype.ext (mul_inv_eq_one.1 h4).symm
  obtain ⟨⟨x, hx⟩, hxo⟩ := Finite.injective_iff_surjective.1 hinj ⟨o, ho⟩
  have hxo' : x⁻¹ * (c * x * c⁻¹) = o := congrArg Subtype.val hxo
  rw [← hxo']
  simp only [hcinv, mul_inv_rev, inv_inv, mul_assoc]
  rw [hc, mul_one]

theorem eq_bot_of_three_involutions (O : Subgroup K) [hO : O.Normal] [Finite O] (a b : K)
    (ha : a * a = 1) (hb : b * b = 1) (hCa : ∀ o ∈ O, o * a = a * o → o = 1)
    (hCb : ∀ o ∈ O, o * b = b * o → o = 1)
    (hCab : ∀ o ∈ O, o * (a * b) = (a * b) * o → o = 1) : O = ⊥ := by
  rw [eq_bot_iff]
  intro o ho
  have h1 := conj_eq_inv_of_fixedPointFree O a ha hCa o ho
  have h2 := conj_eq_inv_of_fixedPointFree O b hb hCb o ho
  have h3 : a * (b * o * b⁻¹) * a⁻¹ = o := by
    rw [h2]
    have : a * o⁻¹ * a⁻¹ = (a * o * a⁻¹)⁻¹ := by group
    rw [this, h1, inv_inv]
  have h4 : o * (a * b) = (a * b) * o := by
    have : (a * b) * o * (a * b)⁻¹ = o := by
      calc (a * b) * o * (a * b)⁻¹ = a * (b * o * b⁻¹) * a⁻¹ := by group
        _ = o := h3
    calc o * (a * b) = (a * b) * o * (a * b)⁻¹ * (a * b) := by rw [this]
      _ = (a * b) * o := by group
  exact Subgroup.mem_bot.2 (hCab o ho h4)

end CFSG.Quasithin.H13.F431.U42
