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

namespace CFSG.RankThree.PartOne.KLR

variable {G : Type*} [Group G]

theorem exists_mul_of_mem_sup_of_commute {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : G} (hg : g ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, g = a * b := by
  rw [Subgroup.sup_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, B.one_mem, (mul_one x).symm⟩
    · exact ⟨1, A.one_mem, x, hx, (one_mul x).symm⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨a', ha', b', hb', rfl⟩ := hy
    refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
    have h : b * a' = a' * b := (hAB a' ha' b hb).symm
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [h]
      _ = a * a' * (b * b') := by group
  | inv x _ hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    have h : Commute a b := hAB a ha b hb
    rw [mul_inv_rev, h.inv_inv.eq]

theorem commute_of_closure {s t : Set G} (h : ∀ x ∈ s, ∀ y ∈ t, x * y = y * x) :
    ∀ x ∈ Subgroup.closure s, ∀ y ∈ Subgroup.closure t, x * y = y * x := by
  have h1 : ∀ x ∈ s, Subgroup.closure t ≤ Subgroup.centralizer {x} := by
    intro x hx
    refine (Subgroup.closure_le _).2 fun y hy => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (h x hx y hy).symm
  have h2 : Subgroup.closure s ≤ Subgroup.centralizer (Subgroup.closure t : Set G) := by
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.1 (h1 x hx hy)
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.1 (h2 hx) y hy).symm

theorem mul_inj_of_disjoint {A B : Subgroup G} (hdisj : A ⊓ B = ⊥) {a a' b b' : G} (ha : a ∈ A)
    (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B) (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ A ⊓ B :=
    ⟨A.mul_mem (A.inv_mem ha') ha, h1 ▸ B.mul_mem hb' (B.inv_mem hb)⟩
  rw [hdisj, Subgroup.mem_bot] at h2
  refine ⟨(inv_mul_eq_one.1 h2).symm, ?_⟩
  rw [h2] at h1
  exact (mul_inv_eq_one.1 h1.symm).symm

theorem fixed_swap {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hdisj : A ⊓ B = ⊥) (φ : G → G)
    (hmul : ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, φ (x * y) = φ x * φ y)
    (hφA : ∀ a ∈ A, φ a ∈ B) (hφB : ∀ b ∈ B, φ b ∈ A)
    (X : Subgroup G) (hX : ∀ a, a ∈ X ↔ a ∈ A ∧ φ (φ a) = a)
    (P : Subgroup G) (hP : ∀ g, g ∈ P ↔ g ∈ A ⊔ B ∧ φ g = g) :
    ∃ Θ : X →* G, Function.Injective Θ ∧ Θ.range = P := by
  have hAle : A ≤ A ⊔ B := le_sup_left
  have hBle : B ≤ A ⊔ B := le_sup_right
  have hφ1 : φ 1 = 1 := by
    have h := hmul 1 (A ⊔ B).one_mem 1 (A ⊔ B).one_mem
    rw [mul_one] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, b * a = a * b := fun a ha b hb => (hAB a ha b hb).symm
  let Θ : X →* G :=
    { toFun := fun x => (x : G) * φ x
      map_one' := by simp [hφ1]
      map_mul' := fun x y => by
        have hxA : (x : G) ∈ A := ((hX x).1 x.2).1
        have hyA : (y : G) ∈ A := ((hX y).1 y.2).1
        have hφx : φ x ∈ B := hφA _ hxA
        have h1 : φ ((x : G) * y) = φ x * φ y := hmul _ (hAle hxA) _ (hAle hyA)
        show (x : G) * y * φ ((x : G) * y) = (x * φ x) * (y * φ y)
        rw [h1]
        calc (x : G) * y * (φ x * φ y) = x * (y * φ x) * φ y := by group
          _ = x * (φ x * y) * φ y := by rw [hcomm _ hyA _ hφx]
          _ = _ := by group }
  have hΘ : ∀ x : X, Θ x = (x : G) * φ x := fun _ => rfl
  refine ⟨Θ, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    have hxA : (x : G) ∈ A := ((hX x).1 x.2).1
    have hφx : φ x ∈ B := hφA _ hxA
    rw [hΘ] at hx
    have := (mul_inj_of_disjoint hdisj hxA A.one_mem hφx B.one_mem (by rw [hx, mul_one])).1
    exact Subtype.ext this
  · ext g
    rw [hP g]
    constructor
    · rintro ⟨x, rfl⟩
      have hxA : (x : G) ∈ A := ((hX x).1 x.2).1
      have hxφ : φ (φ x) = x := ((hX x).1 x.2).2
      have hφx : φ x ∈ B := hφA _ hxA
      refine ⟨?_, ?_⟩
      · rw [hΘ]
        exact (A ⊔ B).mul_mem (hAle hxA) (hBle hφx)
      · rw [hΘ, hmul _ (hAle hxA) _ (hBle hφx), hxφ]
        exact hcomm _ hxA _ hφx
    · rintro ⟨hgAB, hgφ⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hAB hgAB
      have h1 : φ (a * b) = φ a * φ b := hmul _ (hAle ha) _ (hBle hb)
      have hφa : φ a ∈ B := hφA _ ha
      have hφb : φ b ∈ A := hφB _ hb
      rw [h1] at hgφ
      have h2 : a * b = φ b * φ a := by
        rw [← hgφ]
        exact (hAB _ hφb _ hφa).symm
      obtain ⟨hab, hbφ⟩ := mul_inj_of_disjoint hdisj ha hφb hb hφa h2
      have hxX : a ∈ X := (hX a).2 ⟨ha, by rw [← hbφ, hab]⟩
      refine ⟨⟨a, hxX⟩, ?_⟩
      rw [hΘ]
      show a * φ a = a * b
      rw [hbφ]

end CFSG.RankThree.PartOne.KLR
