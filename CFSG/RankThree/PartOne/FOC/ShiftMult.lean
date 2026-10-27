module

public import CFSG.RankThree.PartOne.KC.UnitaryRigidityScalar

public section

namespace CFSG.RankThree.PartOne.FOC

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitaryScalar

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem finrank_primaryComponent_le_of_shift {x : Module.End K V} {u : K}
    (G : V ≃ₗ[K] V) (hG : ∀ v, x (G v) = u • G (x v)) (ν : K) :
    Module.finrank K (primaryComponent x (X - C ν)) ≤
      Module.finrank K (primaryComponent x (X - C (u * ν))) := by
  have hle : (primaryComponent x (X - C ν)).map (G : V →ₗ[K] V) ≤
      primaryComponent x (X - C (u * ν)) := by
    rintro _ ⟨v, hv, rfl⟩
    have hv' : v ∈ primaryComponent x (X - C ν) := hv
    rw [mem_primaryComponent_X_sub_C] at hv' ⊢
    show x (G v) = (u * ν) • G v
    rw [hG v, hv', map_smul, smul_smul]
  have := Submodule.finrank_mono hle
  rwa [LinearEquiv.finrank_map_eq] at this

theorem finrank_primaryComponent_eq_of_shift {x : Module.End K V} {u : K} (hu : IsPrimitiveRoot u 5)
    (G : V ≃ₗ[K] V) (hG : ∀ v, x (G v) = u • G (x v)) (μ : K) (k : ℕ) (hk : k ≤ 5) :
    Module.finrank K (primaryComponent x (X - C (u ^ k * μ))) =
      Module.finrank K (primaryComponent x (X - C μ)) := by
  have hmono : ∀ j k : ℕ, j ≤ k →
      Module.finrank K (primaryComponent x (X - C (u ^ j * μ))) ≤
        Module.finrank K (primaryComponent x (X - C (u ^ k * μ))) := by
    intro j k hjk
    induction k, hjk using Nat.le_induction with
    | base => exact le_rfl
    | succ k hjk ih =>
      refine ih.trans ?_
      have := finrank_primaryComponent_le_of_shift (x := x) G hG (u ^ k * μ)
      rwa [← mul_assoc, ← pow_succ'] at this
  have h5 : u ^ 5 * μ = μ := by rw [hu.pow_eq_one, one_mul]
  apply le_antisymm
  · have := hmono k 5 hk
    rwa [h5] at this
  · have := hmono 0 k (Nat.zero_le k)
    rwa [pow_zero, one_mul] at this

theorem mult_le_one_of_shift (hV : Module.finrank K V = 5) {x : Module.End K V}
    (hsq : Squarefree (minpoly K x))
    (hlin : ∀ a ∈ primaryFactors x, ∃ μ : K, μ ≠ 0 ∧ a = X - C μ) {u : K} (hu : IsPrimitiveRoot u 5)
    (G : V ≃ₗ[K] V) (hG : ∀ v, x (G v) = u • G (x v)) :
    ∀ a ∈ primaryFactors x, primaryMultiplicity x a ≤ 1 := by
  classical
  intro a ha
  obtain ⟨μ, hμ0, rfl⟩ := hlin a ha
  have hne : primaryComponent x (X - C μ) ≠ ⊥ := primaryComponent_ne_bot hsq ha
  have hpos : 0 < Module.finrank K (primaryComponent x (X - C μ)) := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨⟨v, hv⟩, fun h => hv0 (by simpa using congrArg Subtype.val h)⟩
  have hmem : ∀ k : ℕ, k ≤ 5 → (X - C (u ^ k * μ) : K[X]) ∈ primaryFactors x := by
    intro k hk
    have hpos' : 0 < Module.finrank K (primaryComponent x (X - C (u ^ k * μ))) := by
      rw [finrank_primaryComponent_eq_of_shift hu G hG μ k hk]
      exact hpos
    have hne' : primaryComponent x (X - C (u ^ k * μ)) ≠ ⊥ := by
      intro hbot
      rw [hbot] at hpos'
      simp at hpos'
    apply X_sub_C_mem_primaryFactors
    rw [Module.End.hasEigenvalue_iff]
    intro hbot
    apply hne'
    ext v
    rw [mem_primaryComponent_X_sub_C, Submodule.mem_bot]
    constructor
    · intro hv
      have : v ∈ Module.End.eigenspace x (u ^ k * μ) := Module.End.mem_eigenspace_iff.mpr hv
      rw [hbot] at this
      simpa using this
    · rintro rfl
      simp
  have hsum := finrank_eq_sum_primaryComponent (x := x) hsq
  rw [hV] at hsum
  let b : Fin 5 → primaryFactors x := fun k => ⟨X - C (u ^ (k : ℕ) * μ), hmem k (by omega)⟩
  have hbinj : Function.Injective b := by
    intro i j hij
    have h1 : (X - C (u ^ (i : ℕ) * μ) : K[X]) = X - C (u ^ (j : ℕ) * μ) := congrArg Subtype.val hij
    have h2 : u ^ (i : ℕ) * μ = u ^ (j : ℕ) * μ := by
      have := congrArg (fun p : K[X] => p.coeff 0) h1
      simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, neg_inj] at this
      exact this
    have h3 : u ^ (i : ℕ) = u ^ (j : ℕ) := mul_right_cancel₀ hμ0 h2
    exact Fin.ext (hu.pow_inj i.2 j.2 h3)
  have hle : ∑ k : Fin 5, Module.finrank K (primaryComponent x (b k : K[X])) ≤
      ∑ a : primaryFactors x, Module.finrank K (primaryComponent x a) := by
    calc ∑ k : Fin 5, Module.finrank K (primaryComponent x (b k : K[X]))
        = ∑ a ∈ Finset.univ.image b, Module.finrank K (primaryComponent x a) := by
          rw [Finset.sum_image (fun i _ j _ h => hbinj h)]
      _ ≤ ∑ a : primaryFactors x, Module.finrank K (primaryComponent x a) :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hconst : ∀ k : Fin 5, Module.finrank K (primaryComponent x (b k : K[X])) =
      Module.finrank K (primaryComponent x (X - C μ)) := fun k =>
    finrank_primaryComponent_eq_of_shift hu G hG μ k (by omega)
  simp only [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
  rw [← hsum] at hle
  have hmult : primaryMultiplicity x (X - C μ) =
      Module.finrank K (primaryComponent x (X - C μ)) := primaryMultiplicity_X_sub_C x μ
  omega

end CFSG.RankThree.PartOne.FOC
