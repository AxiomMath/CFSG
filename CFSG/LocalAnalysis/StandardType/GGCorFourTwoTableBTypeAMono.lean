module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Diagonal

public section

namespace CFSG.StandardType.TypeA

open Matrix

variable {d : ℕ} {K : Type} [Field K]

@[expose] def rootT (ζ : K) (i j : Fin d) : Fin d → K :=
  fun k => if k = i then ζ else if k = j then ζ⁻¹ else 1

theorem rootT_left (ζ : K) (i j : Fin d) : rootT ζ i j i = ζ := by
  simp [rootT]

theorem rootT_right (ζ : K) {i j : Fin d} (hij : i ≠ j) : rootT ζ i j j = ζ⁻¹ := by
  simp [rootT, Ne.symm hij]

theorem rootT_other (ζ : K) {i j k : Fin d} (hki : k ≠ i) (hkj : k ≠ j) : rootT ζ i j k = 1 := by
  simp [rootT, hki, hkj]

theorem rootT_comp {f : K →* K} (ζ : K) (i j : Fin d) (hf : ∀ x : K, f x⁻¹ = (f x)⁻¹) :
    (fun k => f (rootT ζ i j k)) = rootT (f ζ) i j := by
  funext k
  unfold rootT
  split_ifs <;> simp [hf]

theorem eq_of_mul_rootT {ζ : K} (hζ : ζ ≠ ζ⁻¹) (A : Matrix (Fin d) (Fin d) K)
    (hA : ∀ i j : Fin d, i ≠ j → ∃ D : Fin d → K, A * diagonal (rootT ζ i j) = diagonal D * A)
    {k l l' : Fin d} (hl : A k l ≠ 0) (hl' : A k l' ≠ 0) : l = l' := by
  by_contra hne
  obtain ⟨D, hD⟩ := hA l l' hne
  have h1 := congrFun (congrFun hD k) l
  have h2 := congrFun (congrFun hD k) l'
  rw [mul_diagonal, diagonal_mul, rootT_left, mul_comm] at h1
  rw [mul_diagonal, diagonal_mul, rootT_right ζ hne, mul_comm] at h2
  have e1 : ζ = D k := mul_right_cancel₀ hl h1
  have e2 : ζ⁻¹ = D k := mul_right_cancel₀ hl' h2
  exact hζ (e1.trans e2.symm)

theorem exists_perm_mul_diagonal {ζ : K} (hζ : ζ ≠ ζ⁻¹) (A : GL (Fin d) K)
    (hA : ∀ i j : Fin d, i ≠ j → ∃ D : Fin d → K,
      (A : Matrix (Fin d) (Fin d) K) * diagonal (rootT ζ i j) =
        diagonal D * (A : Matrix (Fin d) (Fin d) K)) :
    ∃ π : Equiv.Perm (Fin d), ∀ u : Fin d → K,
      (A : Matrix (Fin d) (Fin d) K) * diagonal u =
        diagonal (u ∘ π) * (A : Matrix (Fin d) (Fin d) K) := by
  classical
  set M : Matrix (Fin d) (Fin d) K := (A : Matrix (Fin d) (Fin d) K) with hM
  set N : Matrix (Fin d) (Fin d) K := ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) with hN
  have hMN : M * N = 1 := by rw [hM, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hNM : N * M = 1 := by rw [hM, hN, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hrow : ∀ {k l l' : Fin d}, M k l ≠ 0 → M k l' ≠ 0 → l = l' := fun hl hl' =>
    eq_of_mul_rootT hζ M hA hl hl'
  have hex : ∀ k, ∃ l, M k l ≠ 0 := by
    intro k
    have h1 : (M * N) k k = 1 := by rw [hMN, one_apply_eq]
    rw [mul_apply] at h1
    obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h1 ▸ one_ne_zero)
    exact ⟨l, left_ne_zero_of_mul hl⟩
  choose π₀ hπ₀ using hex
  have hsurj : Function.Surjective π₀ := by
    intro l
    have h1 : (N * M) l l = 1 := by rw [hNM, one_apply_eq]
    rw [mul_apply] at h1
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h1 ▸ one_ne_zero)
    exact ⟨k, hrow (hπ₀ k) (right_ne_zero_of_mul hk)⟩
  have hbij : Function.Bijective π₀ := ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  refine ⟨Equiv.ofBijective π₀ hbij, fun u => ?_⟩
  ext k l
  rw [mul_diagonal, diagonal_mul]
  by_cases h : M k l = 0
  · rw [h, zero_mul, mul_zero]
  · have hl : l = π₀ k := hrow h (hπ₀ k)
    simp only [Function.comp_apply, Equiv.ofBijective_apply]
    rw [← hl, mul_comm]

theorem eq_diagonal_of_commute_diagonal (A : Matrix (Fin d) (Fin d) K)
    (h : ∀ u : Fin d → K, A * diagonal u = diagonal u * A) :
    A = diagonal fun i => A i i := by
  classical
  ext k l
  by_cases hkl : k = l
  · rw [hkl, diagonal_apply_eq]
  · rw [diagonal_apply_ne _ hkl]
    have h1 := congrFun (congrFun (h (Pi.single k 1)) k) l
    rw [mul_diagonal, diagonal_mul, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hkl),
      mul_zero, one_mul] at h1
    exact h1.symm

end CFSG.StandardType.TypeA
