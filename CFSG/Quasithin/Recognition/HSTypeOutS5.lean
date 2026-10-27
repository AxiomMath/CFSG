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

namespace CFSG.Quasithin.HSType

@[expose] def c5 : Equiv.Perm (Fin 5) :=
  Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4

@[expose] def c4 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3

@[expose] def evalW5 : List Bool → Equiv.Perm (Fin 5)
  | [] => 1
  | b :: w => (if b then c5 else Equiv.swap 0 1) * evalW5 w

@[expose] def evalW4 : List Bool → Equiv.Perm (Fin 4)
  | [] => 1
  | b :: w => (if b then c4 else Equiv.swap 0 1) * evalW4 w

@[expose] def words5 : List (List Bool) :=
    [[], [false], [true], [true, false], [false, true], [true, true], [false, true, false],
     [true, true, false], [true, false, true], [false, true, true], [true, true, true],
     [true, false, true, false], [false, true, true, false], [true, true, true, false],
     [false, true, false, true], [true, true, false, true], [true, false, true, true],
     [false, true, true, true], [true, true, true, true], [false, true, false, true, false],
     [true, true, false, true, false], [true, false, true, true, false],
     [false, true, true, true, false], [true, true, true, true, false],
     [true, false, true, false, true], [false, true, true, false, true],
     [true, true, true, false, true], [false, true, false, true, true],
     [true, true, false, true, true], [true, false, true, true, true],
     [false, true, true, true, true], [false, true, true, false, true, false],
     [true, true, true, false, true, false], [false, true, false, true, true, false],
     [true, true, false, true, true, false], [true, false, true, true, true, false],
     [true, true, false, true, false, true], [true, false, true, true, false, true],
     [false, true, true, true, false, true], [true, true, true, true, false, true],
     [true, false, true, false, true, true], [false, true, true, false, true, true],
     [true, true, true, false, true, true], [false, true, false, true, true, true],
     [true, true, false, true, true, true], [true, false, true, true, true, true],
     [true, false, true, true, false, true, false], [false, true, true, true, false, true, false],
     [true, true, true, true, false, true, false], [true, false, true, false, true, true, false],
     [false, true, true, false, true, true, false], [true, true, true, false, true, true, false],
     [false, true, false, true, true, true, false], [true, true, false, true, true, true, false],
     [false, true, true, false, true, false, true], [true, true, true, false, true, false, true],
     [false, true, false, true, true, false, true], [true, true, false, true, true, false, true],
     [true, false, true, true, true, false, true], [true, true, false, true, false, true, true],
     [true, false, true, true, false, true, true], [true, true, true, true, false, true, true],
     [true, false, true, false, true, true, true], [true, true, true, false, true, true, true],
     [false, true, false, true, true, true, true], [true, true, false, true, true, true, true],
     [false, true, false, true, true, false, true, false],
     [true, true, false, true, true, false, true, false],
     [true, false, true, true, true, false, true, false],
     [true, true, false, true, false, true, true, false],
     [true, false, true, true, false, true, true, false],
     [true, true, true, true, false, true, true, false],
     [true, false, true, false, true, true, true, false],
     [true, true, true, false, true, true, true, false],
     [true, false, true, true, false, true, false, true],
     [false, true, true, true, false, true, false, true],
     [true, true, true, true, false, true, false, true],
     [true, false, true, false, true, true, false, true],
     [false, true, true, false, true, true, false, true],
     [true, true, true, false, true, true, false, true],
     [false, true, false, true, true, true, false, true],
     [true, true, false, true, true, true, false, true],
     [true, true, true, false, true, false, true, true],
     [false, true, false, true, true, false, true, true],
     [true, true, false, true, false, true, true, true],
     [true, true, true, true, false, true, true, true],
     [true, false, true, false, true, true, true, true],
     [true, true, true, false, true, true, true, true],
     [true, false, true, false, true, true, false, true, false],
     [false, true, true, false, true, true, false, true, false],
     [true, true, true, false, true, true, false, true, false],
     [false, true, false, true, true, true, false, true, false],
     [true, true, true, false, true, false, true, true, false],
     [false, true, false, true, true, false, true, true, false],
     [true, true, false, true, false, true, true, true, false],
     [true, true, true, true, false, true, true, true, false],
     [true, true, false, true, true, false, true, false, true],
     [true, false, true, true, true, false, true, false, true],
     [true, true, false, true, false, true, true, false, true],
     [true, false, true, true, false, true, true, false, true],
     [true, true, true, true, false, true, true, false, true],
     [true, false, true, false, true, true, true, false, true],
     [true, true, true, false, true, true, true, false, true],
     [false, true, true, true, false, true, false, true, true],
     [true, true, true, true, false, true, false, true, true],
     [true, false, true, false, true, true, false, true, true],
     [true, true, false, true, false, true, true, true, true],
     [true, true, false, true, false, true, true, false, true, false],
     [true, false, true, true, false, true, true, false, true, false],
     [true, true, true, true, false, true, true, false, true, false],
     [true, false, true, false, true, true, true, false, true, false],
     [false, true, true, true, false, true, false, true, true, false],
     [true, true, true, true, false, true, false, true, true, false],
     [true, false, true, false, true, true, false, true, true, false],
     [false, true, true, false, true, true, false, true, false, true],
     [true, true, true, false, true, true, false, true, false, true],
     [false, true, false, true, true, true, false, true, false, true],
     [true, true, false, true, false, true, true, false, true, true],
     [true, true, true, true, false, true, true, false, true, false, true],
     [true, false, true, false, true, true, true, false, true, false, true]]

@[expose] def words4 : List (List Bool) :=
    [[], [false], [true], [true, false], [false, true], [true, true], [false, true, false],
     [true, true, false], [true, false, true], [false, true, true], [true, true, true],
     [true, false, true, false], [false, true, true, false], [true, true, true, false],
     [true, true, false, true], [true, false, true, true], [true, true, false, true, false],
     [true, false, true, true, false], [false, true, true, false, true],
     [true, true, true, false, true], [true, true, false, true, true],
     [false, true, true, false, true, false], [true, true, true, false, true, false],
     [true, true, false, true, true, false]]

theorem exists_word5 : ∀ σ : Equiv.Perm (Fin 5), ∃ w ∈ words5, evalW5 w = σ := by
  decide +kernel

theorem exists_word4 : ∀ σ : Equiv.Perm (Fin 4), ∃ w ∈ words4, evalW4 w = σ := by
  decide +kernel

theorem evalW5_mem (w : List Bool) : evalW5 w ∈ Subgroup.closure {Equiv.swap 0 1, c5} := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons b w ih =>
    refine Subgroup.mul_mem _ ?_ ih
    cases b
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem evalW4_mem (w : List Bool) : evalW4 w ∈ Subgroup.closure {Equiv.swap 0 1, c4} := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons b w ih =>
    refine Subgroup.mul_mem _ ?_ ih
    cases b
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem closure_swap_c5 : Subgroup.closure {Equiv.swap (0 : Fin 5) 1, c5} = ⊤ := by
  refine eq_top_iff.mpr fun σ _ => ?_
  obtain ⟨w, -, rfl⟩ := exists_word5 σ
  exact evalW5_mem w

theorem closure_swap_c4 : Subgroup.closure {Equiv.swap (0 : Fin 4) 1, c4} = ⊤ := by
  refine eq_top_iff.mpr fun σ _ => ?_
  obtain ⟨w, -, rfl⟩ := exists_word4 σ
  exact evalW4_mem w

@[expose] def commCount5 (σ : Equiv.Perm (Fin 5)) : ℕ :=
  (Finset.univ.filter fun π : Equiv.Perm (Fin 5) => π * σ = σ * π).card

@[expose] def commCount4 (σ : Equiv.Perm (Fin 4)) : ℕ :=
  (Finset.univ.filter fun π : Equiv.Perm (Fin 4) => π * σ = σ * π).card

theorem isSwap_of_commCount5 : ∀ a : Equiv.Perm (Fin 5), a * a = 1 → a ≠ 1 →
    commCount5 a = 12 → ∃ i j : Fin 5, i ≠ j ∧ a = Equiv.swap i j := by
  decide +kernel

theorem isSwap_of_commCount4 : ∀ a : Equiv.Perm (Fin 4), a * a = 1 → a ≠ 1 →
    commCount4 a = 4 → ∃ i j : Fin 4, i ≠ j ∧ a = Equiv.swap i j := by
  decide +kernel

theorem exists_conj_gens5 : ∀ i j : Fin 5, ∀ b : Equiv.Perm (Fin 5),
    (i ≠ j ∧ b ^ 5 = 1 ∧ b ≠ 1 ∧ (Equiv.swap i j * b) ^ 4 = 1 ∧ (Equiv.swap i j * b) ^ 2 ≠ 1) →
    ∃ ρ : Equiv.Perm (Fin 5), ρ * Equiv.swap 0 1 * ρ⁻¹ = Equiv.swap i j ∧ ρ * c5 * ρ⁻¹ = b := by
  decide +kernel

theorem exists_conj_gens4 : ∀ i j : Fin 4, ∀ b : Equiv.Perm (Fin 4),
    (i ≠ j ∧ b ^ 4 = 1 ∧ b ^ 2 ≠ 1 ∧ (Equiv.swap i j * b) ^ 3 = 1 ∧ Equiv.swap i j * b ≠ 1) →
    ∃ ρ : Equiv.Perm (Fin 4), ρ * Equiv.swap 0 1 * ρ⁻¹ = Equiv.swap i j ∧ ρ * c4 * ρ⁻¹ = b := by
  decide +kernel

theorem commCount5_map (α : Equiv.Perm (Fin 5) ≃* Equiv.Perm (Fin 5)) (σ : Equiv.Perm (Fin 5)) :
    commCount5 (α σ) = commCount5 σ := by
  unfold commCount5
  refine Finset.card_bij (fun π _ => α.symm π) (fun π hπ => ?_) (fun π₁ _ π₂ _ h => ?_)
    (fun π hπ => ⟨α π, ?_, ?_⟩)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
    apply α.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hπ]
  · exact α.symm.injective h
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
    rw [← map_mul, ← map_mul, hπ]
  · exact MulEquiv.symm_apply_apply α π

theorem commCount4_map (α : Equiv.Perm (Fin 4) ≃* Equiv.Perm (Fin 4)) (σ : Equiv.Perm (Fin 4)) :
    commCount4 (α σ) = commCount4 σ := by
  unfold commCount4
  refine Finset.card_bij (fun π _ => α.symm π) (fun π hπ => ?_) (fun π₁ _ π₂ _ h => ?_)
    (fun π hπ => ⟨α π, ?_, ?_⟩)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
    apply α.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hπ]
  · exact α.symm.injective h
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
    rw [← map_mul, ← map_mul, hπ]
  · exact MulEquiv.symm_apply_apply α π

theorem commCount5_swap01 : commCount5 (Equiv.swap 0 1) = 12 := by decide +kernel

theorem commCount4_swap01 : commCount4 (Equiv.swap 0 1) = 4 := by decide +kernel

theorem perm_five_aut_inner (α : Equiv.Perm (Fin 5) ≃* Equiv.Perm (Fin 5)) :
    ∃ ρ : Equiv.Perm (Fin 5), ∀ σ, α σ = ρ * σ * ρ⁻¹ := by
  have ha2 : α (Equiv.swap 0 1) * α (Equiv.swap 0 1) = 1 := by
    rw [← map_mul, Equiv.swap_mul_self, map_one]
  have ha1 : α (Equiv.swap 0 1) ≠ 1 := fun h1 => by
    have := α.injective (h1.trans (map_one α).symm)
    exact absurd this (by decide)
  obtain ⟨i, j, hij, hab⟩ := isSwap_of_commCount5 _ ha2 ha1
    (by rw [commCount5_map, commCount5_swap01])
  have hb5 : α c5 ^ 5 = 1 := by rw [← map_pow, show c5 ^ 5 = 1 by decide, map_one]
  have hb1 : α c5 ≠ 1 := fun h1 => by
    have := α.injective (h1.trans (map_one α).symm)
    exact absurd this (by decide)
  have h4 : (Equiv.swap i j * α c5) ^ 4 = 1 := by
    rw [← hab, ← map_mul, ← map_pow, show (Equiv.swap 0 1 * c5) ^ 4 = 1 by decide, map_one]
  have h2 : (Equiv.swap i j * α c5) ^ 2 ≠ 1 := fun h1 => by
    rw [← hab, ← map_mul, ← map_pow] at h1
    have := α.injective (h1.trans (map_one α).symm)
    exact absurd this (by decide)
  obtain ⟨ρ, hρ1, hρ2⟩ := exists_conj_gens5 i j _ ⟨hij, hb5, hb1, h4, h2⟩
  refine ⟨ρ, fun σ => ?_⟩
  have heq : α.toMonoidHom = (MulAut.conj ρ).toMonoidHom := by
    refine MonoidHom.eq_of_eqOn_dense closure_swap_c5 ?_
    rintro _ (rfl | rfl)
    · show α (Equiv.swap 0 1) = ρ * Equiv.swap 0 1 * ρ⁻¹
      rw [hρ1, hab]
    · show α c5 = ρ * c5 * ρ⁻¹
      rw [hρ2]
  exact congrArg (fun f : Equiv.Perm (Fin 5) →* Equiv.Perm (Fin 5) => f σ) heq

theorem perm_four_aut_inner (α : Equiv.Perm (Fin 4) ≃* Equiv.Perm (Fin 4)) :
    ∃ ρ : Equiv.Perm (Fin 4), ∀ σ, α σ = ρ * σ * ρ⁻¹ := by
  have ha2 : α (Equiv.swap 0 1) * α (Equiv.swap 0 1) = 1 := by
    rw [← map_mul, Equiv.swap_mul_self, map_one]
  have ha1 : α (Equiv.swap 0 1) ≠ 1 := fun h1 => by
    have := α.injective (h1.trans (map_one α).symm)
    exact absurd this (by decide)
  obtain ⟨i, j, hij, hab⟩ := isSwap_of_commCount4 _ ha2 ha1
    (by rw [commCount4_map, commCount4_swap01])
  have hb4 : α c4 ^ 4 = 1 := by rw [← map_pow, show c4 ^ 4 = 1 by decide, map_one]
  have hb2 : α c4 ^ 2 ≠ 1 := fun h1 => by
    rw [← map_pow] at h1
    have := α.injective (h1.trans (map_one α).symm)
    exact absurd this (by decide)
  have h3 : (Equiv.swap i j * α c4) ^ 3 = 1 := by
    rw [← hab, ← map_mul, ← map_pow, show (Equiv.swap 0 1 * c4) ^ 3 = 1 by decide, map_one]
  have h1 : Equiv.swap i j * α c4 ≠ 1 := fun h1 => by
    rw [← hab, ← map_mul] at h1
    have := α.injective (h1.trans (map_one α).symm)
    exact absurd this (by decide)
  obtain ⟨ρ, hρ1, hρ2⟩ := exists_conj_gens4 i j _ ⟨hij, hb4, hb2, h3, h1⟩
  refine ⟨ρ, fun σ => ?_⟩
  have heq : α.toMonoidHom = (MulAut.conj ρ).toMonoidHom := by
    refine MonoidHom.eq_of_eqOn_dense closure_swap_c4 ?_
    rintro _ (rfl | rfl)
    · show α (Equiv.swap 0 1) = ρ * Equiv.swap 0 1 * ρ⁻¹
      rw [hρ1, hab]
    · show α c4 = ρ * c4 * ρ⁻¹
      rw [hρ2]
  exact congrArg (fun f : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 4) => f σ) heq

end CFSG.Quasithin.HSType
