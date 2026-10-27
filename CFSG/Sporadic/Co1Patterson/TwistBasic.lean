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

namespace CFSG.Sporadic.Co1Patterson

theorem split_or_perfect {E L : Type*} [Group E] [Group L] [Group.IsPerfect L] (π : E →* L)
    (hπ : Function.Surjective π) {ζ : E} (hker : ∀ e, π e = 1 ↔ e = 1 ∨ e = ζ) :
    (∃ K : Subgroup E, ζ ∉ K ∧ K.map π = ⊤) ∨ commutator E = ⊤ := by
  have hmap : (commutator E).map π = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hπ,
      ← commutator_def, Group.IsPerfect.commutator_eq_top]
  by_cases hc : ζ ∈ commutator E
  · right
    rw [eq_top_iff]
    intro t _
    have ht : π t ∈ (commutator E).map π := hmap ▸ Subgroup.mem_top _
    obtain ⟨d, hd, hdt⟩ := ht
    have h1 : π (d⁻¹ * t) = 1 := by rw [map_mul, map_inv, hdt, inv_mul_cancel]
    have e : t = d * (d⁻¹ * t) := by group
    rw [e]
    rcases (hker _).mp h1 with h | h
    · rw [h, mul_one]
      exact hd
    · rw [h]
      exact Subgroup.mul_mem _ hd hc
  · exact Or.inl ⟨_, hc, hmap⟩

theorem exists_mulEquiv_comp_eq {W L : Type*} [Group W] [Group L] (f p : W →* L)
    (hf : Function.Surjective f) (hp : Function.Surjective p) (hker : f.ker = p.ker) :
    ∃ α : L ≃* L, ∀ w, f w = α (p w) := by
  refine ⟨(QuotientGroup.quotientKerEquivOfSurjective p hp).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)), fun w => ?_⟩
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective p hp).symm (p w) =
      (QuotientGroup.mk w : W ⧸ p.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1]
  rfl

theorem exists_eq_pow_mul_pow {O : Type*} [Group O] [Finite O] (hO : Nat.card O = 6) {t g : O}
    (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1) (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1) (o : O) :
    ∃ k : Fin 3, ∃ ε : Fin 2, o = t ^ (k : ℕ) * g ^ (ε : ℕ) := by
  have hot : orderOf t = 3 := orderOf_eq_prime ht3 ht1
  have hog : orderOf g = 2 := orderOf_eq_prime hg2 hg1
  have hgt : ∀ a c : ℕ, g ≠ (t ^ c)⁻¹ * t ^ a := fun a c h => by
    have hmem : g ∈ Subgroup.zpowers t := by
      rw [h]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers t c))
        (Subgroup.npow_mem_zpowers t a)
    have := orderOf_dvd_of_mem_zpowers hmem
    rw [hot, hog] at this
    norm_num at this
  let f : Fin 3 × Fin 2 → O := fun x => t ^ (x.1 : ℕ) * g ^ (x.2 : ℕ)
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [f] at h
    have hbd : b = d := by
      by_contra hne
      fin_cases b <;> fin_cases d
      · exact hne rfl
      · simp only [pow_zero, mul_one, pow_one] at h
        exact hgt a c (by rw [h]; group)
      · simp only [pow_one, pow_zero, mul_one] at h
        exact hgt c a (by rw [← h]; group)
      · exact hne rfl
    subst hbd
    have hac : t ^ (a : ℕ) = t ^ (c : ℕ) := mul_right_cancel h
    rw [pow_eq_pow_iff_modEq, hot] at hac
    have : (a : ℕ) = c := by
      have h1 := a.2
      have h2 := c.2
      unfold Nat.ModEq at hac
      rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hac
    rw [Fin.ext this]
  have hbij := hinj.bijective_of_nat_card_le (by rw [hO, Nat.card_eq_fintype_card]; rfl)
  obtain ⟨⟨k, ε⟩, hk⟩ := hbij.2 o
  exact ⟨k, ε, hk.symm⟩

end CFSG.Sporadic.Co1Patterson
