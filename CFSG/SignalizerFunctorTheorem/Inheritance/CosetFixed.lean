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

namespace CFSG.SignalizerFunctorTheorem

theorem exists_fixed_of_coprime {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime) {a : H}
    (ha : a ^ p = 1) (N : Subgroup H) [N.Normal] (hcop : Nat.Coprime p (Nat.card N)) {w : H}
    (hw : a * w * a⁻¹ * w⁻¹ ∈ N) : ∃ x : H, x * w⁻¹ ∈ N ∧ a * x * a⁻¹ = x := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hmap : ∀ x : {x : H // x * w⁻¹ ∈ N}, a * x.1 * a⁻¹ * w⁻¹ ∈ N := by
    intro x
    have h1 : a * (x.1 * w⁻¹) * a⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance _ x.2 a
    have h2 : a * x.1 * a⁻¹ * w⁻¹ = (a * (x.1 * w⁻¹) * a⁻¹) * (a * w * a⁻¹ * w⁻¹) := by group
    rw [h2]
    exact mul_mem h1 hw
  let σ₀ : {x : H // x * w⁻¹ ∈ N} → {x : H // x * w⁻¹ ∈ N} := fun x => ⟨a * x.1 * a⁻¹, hmap x⟩
  have hσ₀ : Function.Injective σ₀ := by
    intro x y hxy
    apply Subtype.ext
    simpa [σ₀] using congrArg Subtype.val hxy
  let σ : Equiv.Perm {x : H // x * w⁻¹ ∈ N} :=
    Equiv.ofBijective σ₀ (Finite.injective_iff_bijective.mp hσ₀)
  have hσapply : ∀ x : {x : H // x * w⁻¹ ∈ N}, (σ x).1 = a * x.1 * a⁻¹ := fun x => rfl
  have hσpow : ∀ (n : ℕ) (x : {x : H // x * w⁻¹ ∈ N}),
      ((σ ^ n) x).1 = a ^ n * x.1 * (a ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, ih (σ x), hσapply x, pow_succ]
      group
  have hσ : σ ^ p ^ 1 = 1 := by
    ext x
    rw [pow_one, hσpow, ha]
    simp
  have : Fintype {x : H // x * w⁻¹ ∈ N} := Fintype.ofFinite _
  have hcard : ¬ p ∣ Fintype.card {x : H // x * w⁻¹ ∈ N} := by
    rw [Fintype.card_eq_nat_card]
    let e : {x : H // x * w⁻¹ ∈ N} ≃ N :=
      { toFun := fun x => ⟨x.1 * w⁻¹, x.2⟩
        invFun := fun n => ⟨n.1 * w, by simp⟩
        left_inv := fun x => by ext; simp
        right_inv := fun n => by ext; simp }
    rw [Nat.card_congr e]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp hcop
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hσ
  refine ⟨x.1, x.2, ?_⟩
  have := congrArg Subtype.val hx
  simpa [σ, σ₀] using this

end CFSG.SignalizerFunctorTheorem
