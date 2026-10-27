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
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.G105

open Equiv

abbrev G0 : Type := Perm (Fin 3) × Perm (Fin 3)

@[expose] def E9 : Subgroup G0 := (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3))

theorem mem_E9 {g : G0} : g ∈ E9 ↔ Perm.sign g.1 = 1 ∧ Perm.sign g.2 = 1 := by
  simp [E9, Subgroup.mem_prod, Perm.mem_alternatingGroup]

theorem perm3_sq_of_sign_neg {τ : Perm (Fin 3)} (h : Perm.sign τ = -1) : τ * τ = 1 := by
  have key : ∀ τ : Perm (Fin 3), Perm.sign τ = -1 → τ * τ = 1 := by decide
  exact key τ h

theorem E9_normal : E9.Normal := by
  constructor
  intro n hn g
  rw [mem_E9] at hn ⊢
  simp [hn.1, hn.2]

theorem card_E9 : Nat.card E9 = 9 := by
  have h : Nat.card E9 = Nat.card {g : G0 // Perm.sign g.1 = 1 ∧ Perm.sign g.2 = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_E9)
  rw [h, Nat.card_eq_fintype_card]
  decide

theorem perm3_pow_three {σ : Perm (Fin 3)} (h : Perm.sign σ = 1) : σ ^ 3 = 1 := by
  have key : ∀ τ : Perm (Fin 3), Perm.sign τ = 1 → τ ^ 3 = 1 := by decide
  exact key σ h

theorem perm3_conj_inv {τ σ : Perm (Fin 3)} (hτ : Perm.sign τ = -1) (hσ : Perm.sign σ = 1) :
    τ * σ * τ⁻¹ = σ⁻¹ := by
  have key : ∀ τ σ : Perm (Fin 3), Perm.sign τ = -1 → Perm.sign σ = 1 →
      τ * σ * τ⁻¹ = σ⁻¹ := by decide
  exact key τ σ hτ hσ

theorem perm3_eq_one_of_sq {σ : Perm (Fin 3)} (h2 : σ ^ 2 = 1) (hs : Perm.sign σ = 1) :
    σ = 1 := by
  have key : ∀ σ : Perm (Fin 3), σ ^ 2 = 1 → Perm.sign σ = 1 → σ = 1 := by decide
  exact key σ h2 hs

theorem perm3_comm {σ τ : Perm (Fin 3)} (hσ : Perm.sign σ = 1) (hτ : Perm.sign τ = 1) :
    σ * τ = τ * σ := by
  have key : ∀ σ τ : Perm (Fin 3), Perm.sign σ = 1 → Perm.sign τ = 1 → σ * τ = τ * σ := by
    decide
  exact key σ τ hσ hτ

theorem sign_eq_one_of_pow_three_pow (k : ℕ) {σ : Perm (Fin 3)} (h : σ ^ (3 ^ k) = 1) :
    Perm.sign σ = 1 := by
  rcases Int.units_eq_one_or (Perm.sign σ) with h1 | h1
  · exact h1
  · have h2 : (Perm.sign σ) ^ (3 ^ k) = 1 := by
      rw [← map_pow, h, map_one]
    rw [h1, Odd.neg_one_pow (Odd.pow (by decide))] at h2
    exact absurd h2 (by decide)

theorem mem_E9_of_pow_three_pow (k : ℕ) {g : G0} (h : g ^ (3 ^ k) = 1) : g ∈ E9 := by
  rw [mem_E9]
  have h1 : g.1 ^ (3 ^ k) = 1 := by
    have := congrArg Prod.fst h
    simpa using this
  have h2 : g.2 ^ (3 ^ k) = 1 := by
    have := congrArg Prod.snd h
    simpa using this
  exact ⟨sign_eq_one_of_pow_three_pow k h1, sign_eq_one_of_pow_three_pow k h2⟩

theorem pow_three_of_mem_E9 {g : G0} (hg : g ∈ E9) : g ^ 3 = 1 := by
  rw [mem_E9] at hg
  exact Prod.ext (by simpa using perm3_pow_three hg.1) (by simpa using perm3_pow_three hg.2)

theorem mul_comm_of_mem_E9 {g h : G0} (hg : g ∈ E9) (hh : h ∈ E9) : g * h = h * g := by
  rw [mem_E9] at hg hh
  exact Prod.ext (perm3_comm hg.1 hh.1) (perm3_comm hg.2 hh.2)

theorem sign_pair_cases (x : G0) :
    (Perm.sign x.1 = 1 ∧ Perm.sign x.2 = 1) ∨ (Perm.sign x.1 = -1 ∧ Perm.sign x.2 = -1) ∨
      (Perm.sign x.1 = 1 ∧ Perm.sign x.2 = -1) ∨ (Perm.sign x.1 = -1 ∧ Perm.sign x.2 = 1) := by
  rcases Int.units_eq_one_or (Perm.sign x.1) with h1 | h1 <;>
    rcases Int.units_eq_one_or (Perm.sign x.2) with h2 | h2 <;> simp [h1, h2]

theorem sign_split (R : Subgroup G0) (hE : E9 ≤ R) {ψ : G0} (hψ : ψ ∈ R)
    (hψ1 : Perm.sign ψ.1 = -1) (hψ2 : Perm.sign ψ.2 = -1) :
    (∀ g ∈ R, Perm.sign g.1 = Perm.sign g.2) ∨ R = ⊤ := by
  by_cases h : ∀ g ∈ R, Perm.sign g.1 = Perm.sign g.2
  · exact Or.inl h
  · right
    push Not at h
    obtain ⟨g₀, hg₀, hne⟩ := h
    have realize : ∀ x : G0, ∃ r ∈ R, Perm.sign r.1 = Perm.sign x.1 ∧
        Perm.sign r.2 = Perm.sign x.2 := by
      intro x
      rcases sign_pair_cases x with hx | hx | hx | hx
      · exact ⟨1, R.one_mem, by simp [hx.1, hx.2]⟩
      · exact ⟨ψ, hψ, by simp [hx.1, hx.2, hψ1, hψ2]⟩
      · rcases sign_pair_cases g₀ with hg | hg | hg | hg
        · exact absurd (hg.1.trans hg.2.symm) hne
        · exact absurd (hg.1.trans hg.2.symm) hne
        · exact ⟨g₀, hg₀, by simp [hx.1, hx.2, hg.1, hg.2]⟩
        · exact ⟨g₀ * ψ, R.mul_mem hg₀ hψ, by
            simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
            rw [hg.1, hg.2, hψ1, hψ2, hx.1, hx.2]
            decide⟩
      · rcases sign_pair_cases g₀ with hg | hg | hg | hg
        · exact absurd (hg.1.trans hg.2.symm) hne
        · exact absurd (hg.1.trans hg.2.symm) hne
        · exact ⟨g₀ * ψ, R.mul_mem hg₀ hψ, by
            simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
            rw [hg.1, hg.2, hψ1, hψ2, hx.1, hx.2]
            decide⟩
        · exact ⟨g₀, hg₀, by simp [hx.1, hx.2, hg.1, hg.2]⟩
    rw [eq_top_iff]
    intro x _
    obtain ⟨r, hr, hsr1, hsr2⟩ := realize x
    have hxr : x * r⁻¹ ∈ E9 := by
      rw [mem_E9]
      simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv, map_mul, map_inv]
      rw [hsr1, hsr2]
      exact ⟨by simp, by simp⟩
    have : x = (x * r⁻¹) * r := by group
    rw [this]
    exact R.mul_mem (hE hxr) hr

end CFSG.Quasithin.G105
