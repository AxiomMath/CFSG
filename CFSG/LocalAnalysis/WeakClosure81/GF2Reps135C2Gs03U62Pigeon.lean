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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.WeakClosure81

@[expose] def gs03FixCount {α : Type} [Fintype α] [DecidableEq α] (g : Equiv.Perm α) : ℕ :=
  (Finset.univ.filter fun p => g p = p).card

theorem gs03FixCount_conj {α : Type} [Fintype α] [DecidableEq α] (c g : Equiv.Perm α) :
    gs03FixCount (c * g * c⁻¹) = gs03FixCount g := by
  unfold gs03FixCount
  refine Finset.card_bij (fun p _ => c⁻¹ p) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    simpa [Equiv.Perm.mul_apply] using congrArg (fun x => c⁻¹ x) hp
  · intro p _ q _ hpq
    exact (c⁻¹).injective hpq
  · intro q hq
    refine ⟨c q, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    simp [Equiv.Perm.mul_apply, hq]

theorem gs03_two_class_cover {Γ : Type} [Group Γ] {X : Set Γ} {ρ₁ ρ₂ g₀ g₁ : Γ}
    (hX : ∀ a ∈ X, IsConj ρ₁ a ∨ IsConj ρ₂ a) (h0 : g₀ ∈ X) (h1 : g₁ ∈ X)
    (hn : ¬ IsConj g₀ g₁) : ∀ a ∈ X, IsConj g₀ a ∨ IsConj g₁ a := by
  intro a ha
  have hg0 := hX g₀ h0
  have hg1 := hX g₁ h1
  rcases hX a ha with ha1 | ha2
  · rcases hg0 with hg01 | hg02
    · exact Or.inl (hg01.symm.trans ha1)
    · rcases hg1 with hg11 | hg12
      · exact Or.inr (hg11.symm.trans ha1)
      · exact absurd (hg02.symm.trans hg12) hn
  · rcases hg0 with hg01 | hg02
    · rcases hg1 with hg11 | hg12
      · exact absurd (hg01.symm.trans hg11) hn
      · exact Or.inr (hg12.symm.trans ha2)
    · exact Or.inl (hg02.symm.trans ha2)

theorem gs03_witness_pad {S Ω : Type} [Group S] (ι : S →* Equiv.Perm Ω) (g : Equiv.Perm Ω)
    {k k' : ℕ} (hk : 0 < k) (hkk : k ≤ k')
    (h : ∃ s : Fin k → S,
      ι.range ≤ Subgroup.closure (Set.range fun i => (ι (s i))⁻¹ * g * ι (s i))) :
    ∃ s : Fin k' → S,
      ι.range ≤ Subgroup.closure (Set.range fun i => (ι (s i))⁻¹ * g * ι (s i)) := by
  obtain ⟨s, hs⟩ := h
  have hk1 : k - 1 < k := by omega
  let s' : Fin k' → S := fun i => s ⟨min i.val (k - 1),
    lt_of_le_of_lt (Nat.min_le_right _ _) hk1⟩
  refine ⟨s', ?_⟩
  have hsub : Set.range (fun i : Fin k => (ι (s i))⁻¹ * g * ι (s i)) ⊆
      Set.range (fun i : Fin k' => (ι (s' i))⁻¹ * g * ι (s' i)) := by
    rintro y ⟨j, rfl⟩
    refine ⟨⟨j.val, j.isLt.trans_le hkk⟩, ?_⟩
    have hsj : s' ⟨j.val, j.isLt.trans_le hkk⟩ = s j := by
      dsimp only [s']
      congr 1
      apply Fin.ext
      exact Nat.min_eq_left (by omega)
    dsimp only
    rw [hsj]
  exact le_trans hs (Subgroup.closure_mono hsub)

end CFSG.LocalAnalysis.WeakClosure81
