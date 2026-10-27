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

namespace CFSG.Quasithin.H13

open scoped commutatorElement

@[expose] def NormalDichotomy (Γ : Type*) [Group Γ] : Prop :=
  ∀ N : Subgroup Γ, N.Normal → N ≤ Subgroup.center Γ ∨ N = ⊤

theorem NormalDichotomy.of_isSimpleGroup {Γ : Type*} [Group Γ] (h : IsSimpleGroup Γ) :
    NormalDichotomy Γ := fun N hN => by
  have := hN
  rcases h.eq_bot_or_eq_top_of_normal N with h1 | h1
  · exact Or.inl (h1 ▸ bot_le)
  · exact Or.inr h1

theorem NormalDichotomy.of_perfect_simple_quotient {Γ : Type*} [Group Γ] (hperf : commutator Γ = ⊤)
    (hs : IsSimpleGroup (Γ ⧸ Subgroup.center Γ)) : NormalDichotomy Γ := fun N hN => by
  have hn : (N.map (QuotientGroup.mk' (Subgroup.center Γ))).Normal :=
    hN.map _ (QuotientGroup.mk'_surjective _)
  have := hn
  rcases hs.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (Subgroup.center Γ))) with h1 | h1
  · left
    intro n hn'
    have : QuotientGroup.mk' (Subgroup.center Γ) n ∈
        N.map (QuotientGroup.mk' (Subgroup.center Γ)) :=
      Subgroup.mem_map_of_mem _ hn'
    rw [h1, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff _).mp this
  · right
    have hsplit : ∀ g : Γ, ∃ n ∈ N, ∃ z ∈ Subgroup.center Γ, g = n * z := fun g => by
      have : QuotientGroup.mk' (Subgroup.center Γ) g ∈
          N.map (QuotientGroup.mk' (Subgroup.center Γ)) := by
        rw [h1]
        exact Subgroup.mem_top _
      obtain ⟨n, hn', hnk⟩ := Subgroup.mem_map.mp this
      refine ⟨n, hn', n⁻¹ * g, ?_, by group⟩
      have h2 : QuotientGroup.mk' (Subgroup.center Γ) (n⁻¹ * g) = 1 := by
        rw [map_mul, map_inv, hnk, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h2
    rw [eq_top_iff, ← hperf, commutator_def]
    refine Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => ?_
    obtain ⟨n₁, hn₁, z₁, hz₁, rfl⟩ := hsplit g₁
    obtain ⟨n₂, hn₂, z₂, hz₂, rfl⟩ := hsplit g₂
    have hz1 : ⁅z₁, n₂⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz₁ n₂).symm
    have hw1 : ⁅n₁ * z₁, z₂⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz₂ (n₁ * z₁))
    have e : ⁅n₁ * z₁, n₂ * z₂⁆ = ⁅n₁, n₂⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj, hw1, commutatorElement_mul_left_eq_conj_mul,
        hz1]
      group
    rw [e]
    exact N.mul_mem (N.mul_mem (N.mul_mem hn₁ hn₂) (N.inv_mem hn₁)) (N.inv_mem hn₂)

theorem normal_of_commuting_sup {A : Type*} [Group A] {A₁ A₂ : Subgroup A}
    (hsup : A₁ ⊔ A₂ = ⊤) (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) : A₁.Normal := by
  have hN₂ : A₂ ≤ Subgroup.normalizer (A₁ : Set A) := fun b hb => by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨fun ha => ?_, fun ha => ?_⟩
    · have : b * a * b⁻¹ = a := by
        rw [mul_inv_eq_iff_eq_mul]
        exact (hcomm a ha b hb).symm
      rw [this]
      exact ha
    · have h1 := hcomm _ ha b⁻¹ (A₂.inv_mem hb)
      have h2 : a = b * a * b⁻¹ :=
        calc a = b⁻¹ * (b * a * b⁻¹) * b := by group
          _ = b * a * b⁻¹ * b⁻¹ * b := by rw [← h1]
          _ = b * a * b⁻¹ := by group
      rw [h2]
      exact ha
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
  exact sup_le Subgroup.le_normalizer hN₂

theorem false_of_commuting_pair {Γ A : Type*} [Group Γ] [Group A] (π : Γ →* A)
    (hπ : Function.Surjective π) (hQ : NormalDichotomy Γ) {A₁ A₂ : Subgroup A}
    (hsup : A₁ ⊔ A₂ = ⊤) (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a)
    (h₁ : ¬ A₁ ≤ Subgroup.center A) (h₂ : ¬ A₂ ≤ Subgroup.center A) : False := by
  have hN : A₁.Normal := normal_of_commuting_sup hsup hcomm
  rcases hQ (A₁.comap π) (hN.comap π) with hc | hT
  · apply h₁
    intro a ha
    obtain ⟨g, rfl⟩ := hπ a
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨h, rfl⟩ := hπ x
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hc ha) h]
  · apply h₂
    intro b hb
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨g, rfl⟩ := hπ x
    have : π g ∈ A₁ := by
      have : g ∈ A₁.comap π := hT ▸ Subgroup.mem_top g
      exact this
    exact (hcomm _ this b hb)

end CFSG.Quasithin.H13
