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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.OddAvg

variable {K : Type*} [Group K] {M N : Type*} [AddCommGroup M] [AddCommGroup N]

@[expose] def avgTerm (ρ : K →* AddMonoid.End M) (σ : K →* AddMonoid.End N) (B : Subgroup K)
    (φ₀ : N →+ M) (hφ₀ : ∀ b ∈ B, ∀ x, φ₀ (σ b x) = ρ b (φ₀ x)) (x : N) : K ⧸ B → M :=
  Quotient.lift (fun g : K => ρ g (φ₀ (σ g⁻¹ x))) (fun g g' hgg => by
    have h : g⁻¹ * g' ∈ B := QuotientGroup.leftRel_apply.mp hgg
    have hρ : ∀ (a b : K) (m : M), ρ (a * b) m = ρ a (ρ b m) := fun a b m => by
      rw [map_mul]; rfl
    have hσ : ∀ (a b : K) (y : N), σ (a * b) y = σ a (σ b y) := fun a b y => by
      rw [map_mul]; rfl
    obtain ⟨b, hb, rfl⟩ : ∃ b ∈ B, g' = g * b := ⟨g⁻¹ * g', h, by group⟩
    show ρ g (φ₀ (σ g⁻¹ x)) = ρ (g * b) (φ₀ (σ (g * b)⁻¹ x))
    rw [mul_inv_rev, hσ, hρ, ← hφ₀ b hb, ← hσ, mul_inv_cancel, map_one]
    rfl)

theorem avgTerm_mk (ρ : K →* AddMonoid.End M) (σ : K →* AddMonoid.End N) (B : Subgroup K)
    (φ₀ : N →+ M) (hφ₀ : ∀ b ∈ B, ∀ x, φ₀ (σ b x) = ρ b (φ₀ x)) (x : N) (g : K) :
    avgTerm ρ σ B φ₀ hφ₀ x (g : K ⧸ B) = ρ g (φ₀ (σ g⁻¹ x)) := rfl

@[expose] noncomputable def avgMap (ρ : K →* AddMonoid.End M)
    (σ : K →* AddMonoid.End N) (B : Subgroup K) [Fintype (K ⧸ B)] (φ₀ : N →+ M)
    (hφ₀ : ∀ b ∈ B, ∀ x, φ₀ (σ b x) = ρ b (φ₀ x)) : N →+ M where
  toFun x := ∑ q, avgTerm ρ σ B φ₀ hφ₀ x q
  map_zero' := by
    refine Finset.sum_eq_zero fun q _ => ?_
    induction q using Quotient.inductionOn
    rw [avgTerm_mk, map_zero, map_zero, map_zero]
  map_add' x y := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    induction q using Quotient.inductionOn
    rw [avgTerm_mk, avgTerm_mk, avgTerm_mk, map_add, map_add, map_add]

theorem avgMap_apply (ρ : K →* AddMonoid.End M) (σ : K →* AddMonoid.End N)
    (B : Subgroup K) [Fintype (K ⧸ B)] (φ₀ : N →+ M)
    (hφ₀ : ∀ b ∈ B, ∀ x, φ₀ (σ b x) = ρ b (φ₀ x)) (x : N) :
    avgMap ρ σ B φ₀ hφ₀ x = ∑ q, avgTerm ρ σ B φ₀ hφ₀ x q := rfl

theorem avgMap_equivariant (ρ : K →* AddMonoid.End M)
    (σ : K →* AddMonoid.End N) (B : Subgroup K) [Fintype (K ⧸ B)] (φ₀ : N →+ M)
    (hφ₀ : ∀ b ∈ B, ∀ x, φ₀ (σ b x) = ρ b (φ₀ x)) (h : K) (x : N) :
    avgMap ρ σ B φ₀ hφ₀ (σ h x) = ρ h (avgMap ρ σ B φ₀ hφ₀ x) := by
  rw [avgMap_apply, avgMap_apply, map_sum]
  have hterm : ∀ q : K ⧸ B,
      avgTerm ρ σ B φ₀ hφ₀ (σ h x) q = ρ h (avgTerm ρ σ B φ₀ hφ₀ x (h⁻¹ • q)) := by
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      show avgTerm ρ σ B φ₀ hφ₀ (σ h x) (g : K ⧸ B) =
        ρ h (avgTerm ρ σ B φ₀ hφ₀ x ((h⁻¹ * g : K) : K ⧸ B))
      rw [avgTerm_mk, avgTerm_mk]
      have hρ : ∀ (a b : K) (m : M), ρ (a * b) m = ρ a (ρ b m) := fun a b m => by
        rw [map_mul]; rfl
      have hσ : ∀ (a b : K) (y : N), σ (a * b) y = σ a (σ b y) := fun a b y => by
        rw [map_mul]; rfl
      rw [← hσ, ← hρ, mul_inv_cancel_left, mul_inv_rev, inv_inv]
  simp_rw [hterm]
  exact Fintype.sum_equiv (MulAction.toPerm h⁻¹) _ _ fun q => rfl

theorem nsmul_eq_self_of_odd {n : ℕ} (hn : Odd n) {x : N} (hx : x + x = 0) : n • x = x := by
  obtain ⟨k, rfl⟩ := hn
  rw [add_nsmul, one_nsmul, two_mul, add_nsmul, ← nsmul_add, hx, nsmul_zero, zero_add]

theorem exists_equivariant_section_of_odd_index [Finite K] (ρ : K →* AddMonoid.End M)
    (σ : K →* AddMonoid.End N) (B : Subgroup K) (hB : Odd B.index)
    (hN : ∀ x : N, x + x = 0) (f : M →+ N) (hf : ∀ (g : K) (m : M), f (ρ g m) = σ g (f m))
    (s₀ : N →+ M) (hs₀ : ∀ x, f (s₀ x) = x) (hs₀B : ∀ b ∈ B, ∀ x, s₀ (σ b x) = ρ b (s₀ x)) :
    ∃ s : N →+ M, (∀ x, f (s x) = x) ∧ ∀ (g : K) (x : N), s (σ g x) = ρ g (s x) := by
  classical
  have _ : Fintype (K ⧸ B) := Fintype.ofFinite _
  refine ⟨avgMap ρ σ B s₀ hs₀B, fun x => ?_, avgMap_equivariant ρ σ B s₀ hs₀B⟩
  rw [avgMap_apply, map_sum]
  have hterm : ∀ q : K ⧸ B, f (avgTerm ρ σ B s₀ hs₀B x q) = x := by
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      show f (avgTerm ρ σ B s₀ hs₀B x (g : K ⧸ B)) = x
      rw [avgTerm_mk, hf, hs₀, show σ g (σ g⁻¹ x) = σ (g * g⁻¹) x by rw [map_mul]; rfl,
        mul_inv_cancel, map_one]
      rfl
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
  exact nsmul_eq_self_of_odd hB (hN x)

theorem exists_equivariant_retraction_of_odd_index [Finite K] (ρ : K →* AddMonoid.End M)
    (σ : K →* AddMonoid.End N) (B : Subgroup K) (hB : Odd B.index)
    (hN : ∀ x : N, x + x = 0) (f : N →+ M) (hf : ∀ (g : K) (x : N), f (σ g x) = ρ g (f x))
    (p₀ : M →+ N) (hp₀ : ∀ x, p₀ (f x) = x) (hp₀B : ∀ b ∈ B, ∀ m, p₀ (ρ b m) = σ b (p₀ m)) :
    ∃ p : M →+ N, (∀ x, p (f x) = x) ∧ ∀ (g : K) (m : M), p (ρ g m) = σ g (p m) := by
  classical
  have _ : Fintype (K ⧸ B) := Fintype.ofFinite _
  refine ⟨avgMap σ ρ B p₀ hp₀B, fun x => ?_, avgMap_equivariant σ ρ B p₀ hp₀B⟩
  rw [avgMap_apply]
  have hterm : ∀ q : K ⧸ B, avgTerm σ ρ B p₀ hp₀B (f x) q = x := by
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      show avgTerm σ ρ B p₀ hp₀B (f x) (g : K ⧸ B) = x
      rw [avgTerm_mk, ← hf, hp₀, show σ g (σ g⁻¹ x) = σ (g * g⁻¹) x by rw [map_mul]; rfl,
        mul_inv_cancel, map_one]
      rfl
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
  exact nsmul_eq_self_of_odd hB (hN x)

end CFSG.Quasithin.OddAvg
