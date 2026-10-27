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
public import Mathlib.GroupTheory.IsPerfect
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

namespace CFSG.Quasithin.S146zU.UG1

section Perfect

variable {P E Y : Type*} [Group P] [CommGroup E] [CommGroup Y]

theorem commutator_mem_map_of_isPerfect [Group.IsPerfect P] (σE : P →* MulAut E)
    (σY : P →* MulAut Y) (ι : E →* Y) (hι : ∀ p e, ι (σE p e) = σY p (ι e))
    (hrange : ∀ p y, σY p y * y⁻¹ ∈ ι.range) {A : Subgroup E}
    (hA : ∀ p e, σE p e * e⁻¹ ∈ A) (p : P) (y : Y) : σY p y * y⁻¹ ∈ A.map ι := by
  let S : Subgroup Y := A.map ι
  let φ : P →* Y ⧸ S :=
    { toFun := fun p => ((σY p y * y⁻¹ : Y) : Y ⧸ S)
      map_one' := by simp
      map_mul' := fun p q => by
        obtain ⟨e, he⟩ := hrange q y
        have hq : σY q y = ι e * y := by rw [he, inv_mul_cancel_right]
        have h1 : σY (p * q) y = ι (σE p e) * σY p y := by
          rw [map_mul, MulAut.mul_apply, hq, map_mul, hι]
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
        refine ⟨(σE p e * e⁻¹)⁻¹, A.inv_mem (hA p e), ?_⟩
        rw [h1, ← he]
        simp only [map_inv, map_mul]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel }
  have h1 : φ p = 1 :=
    Abelianization.commutator_subset_ker φ (Group.IsPerfect.mem_commutator (G := P) (g := p))
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem fix_of_isPerfect [Group.IsPerfect P] (σE : P →* MulAut E) (σY : P →* MulAut Y)
    (ι : E →* Y) (hι : ∀ p e, ι (σE p e) = σY p (ι e)) (hrange : ∀ p y, σY p y * y⁻¹ ∈ ι.range)
    {A : Subgroup E} (hA : ∀ p e, σE p e * e⁻¹ ∈ A) {α : MulAut E} {β : MulAut Y}
    (hαβ : ∀ e, ι (α e) = β (ι e)) (hAα : ∀ a ∈ A, α a = a) (p : P) (y : Y) :
    β (σY p y * y⁻¹) = σY p y * y⁻¹ := by
  obtain ⟨a, ha, h⟩ := commutator_mem_map_of_isPerfect σE σY ι hι hrange hA p y
  rw [← h, ← hαβ, hAα a ha]

end Perfect

section Swap

variable {Y : Type*} [CommGroup Y]

theorem fix_swap {a b : MulAut Y} (hab : a * b = b * a) (h : ∀ y : Y, a (b y * y⁻¹) = b y * y⁻¹)
    (y : Y) : b (a y * y⁻¹) = a y * y⁻¹ := by
  have h1 : b (a y) = a (b y) := by
    have := congrArg (fun f : MulAut Y => f y) hab.symm
    simpa using this
  have h2 : a (b y) * (a y)⁻¹ = b y * y⁻¹ := by
    have := h y
    rwa [map_mul, map_inv] at this
  have h3 : a (b y) = b y * y⁻¹ * a y := by
    rw [← h2]
    group
  rw [map_mul, map_inv, h1, h3]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Swap

end CFSG.Quasithin.S146zU.UG1
