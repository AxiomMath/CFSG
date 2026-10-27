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

namespace CFSG.Quasithin.H13.AS91

theorem cocycle_odd_index {K A : Type*} [Group K] [Finite K] [CommGroup A] [Finite A]
    (ρ : K →* MulAut A) (T : Subgroup K) (hodd : Odd T.index) (hexp : ∀ a : A, a * a = 1)
    (e : K → A) (hcoc : ∀ k l, e (k * l) = e k * ρ k (e l)) (hT : ∀ t ∈ T, e t = 1) :
    ∃ w : A, ∀ k, e k = w * (ρ k w)⁻¹ := by
  classical
  have hconst : ∀ k t, t ∈ T → e (k * t) = e k := by
    intro k t ht
    rw [hcoc, hT t ht, map_one, mul_one]
  have hwd : ∀ a b : K, QuotientGroup.leftRel T a b → e a = e b := by
    intro a b h
    rw [QuotientGroup.leftRel_apply] at h
    have h' := hconst a (a⁻¹ * b) h
    rw [mul_inv_cancel_left] at h'
    exact h'.symm
  obtain ⟨E', hE'⟩ : ∃ E' : K ⧸ T → A, ∀ k : K, E' (k : K ⧸ T) = e k :=
    ⟨Quotient.lift e hwd, fun k => rfl⟩
  have hmul : ∀ (k₀ : K) (q : K ⧸ T), E' (k₀ • q) = e k₀ * ρ k₀ (E' q) := by
    intro k₀ q
    refine QuotientGroup.induction_on q (fun z => ?_)
    show E' (k₀ • ((z : K) : K ⧸ T)) = e k₀ * ρ k₀ (E' ((z : K) : K ⧸ T))
    have hsm : k₀ • ((z : K) : K ⧸ T) = ((k₀ * z : K) : K ⧸ T) := rfl
    rw [hsm, hE', hE', hcoc]
  haveI : Fintype (K ⧸ T) := Fintype.ofFinite _
  have hcard : Fintype.card (K ⧸ T) = T.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  obtain ⟨w, hw⟩ : ∃ w : A, w = ∏ q : K ⧸ T, E' q := ⟨_, rfl⟩
  refine ⟨w, fun k₀ => ?_⟩
  obtain ⟨m, hm⟩ := hodd
  have hpow : e k₀ ^ T.index = e k₀ := by
    rw [hm, pow_succ, pow_mul, sq, hexp (e k₀), one_pow, one_mul]
  have h1 : ∏ q : K ⧸ T, E' (k₀ • q) = ∏ q : K ⧸ T, E' q :=
    Fintype.prod_bijective (fun q : K ⧸ T => k₀ • q) (MulAction.bijective k₀) _ _ (fun _ => rfl)
  have h2 : ∏ q : K ⧸ T, E' (k₀ • q) = ∏ q : K ⧸ T, e k₀ * ρ k₀ (E' q) :=
    Finset.prod_congr rfl (fun q _ => hmul k₀ q)
  have h3 : ∏ q : K ⧸ T, e k₀ * ρ k₀ (E' q) = e k₀ ^ Fintype.card (K ⧸ T) * ρ k₀ w := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hw, map_prod]
  have hfix : w = e k₀ * ρ k₀ w := by
    calc w = ∏ q : K ⧸ T, E' q := hw
      _ = ∏ q : K ⧸ T, E' (k₀ • q) := h1.symm
      _ = ∏ q : K ⧸ T, e k₀ * ρ k₀ (E' q) := h2
      _ = e k₀ ^ Fintype.card (K ⧸ T) * ρ k₀ w := h3
      _ = e k₀ * ρ k₀ w := by rw [hcard, hpow]
  exact eq_mul_inv_of_mul_eq hfix.symm

end CFSG.Quasithin.H13.AS91
