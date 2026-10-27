module

public import CFSG.RankThree.Chevalley.SteinbergBUF4A2CubicDescent

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix Polynomial

section Cubic

variable (K : Type) [Field K] [Fintype K] [CharP K 2]

theorem exists_ne_cube_add_sq : ∃ c : K, ∀ t : K, t ^ 3 + t ^ 2 ≠ c := by
  by_contra h
  push Not at h
  have hinj : Function.Injective (fun t : K => t ^ 3 + t ^ 2) :=
    Finite.injective_iff_surjective.2 h
  have e : (fun t : K => t ^ 3 + t ^ 2) 0 = (fun t : K => t ^ 3 + t ^ 2) 1 := by
    change (0 : K) ^ 3 + 0 ^ 2 = 1 ^ 3 + 1 ^ 2
    rw [zero_pow three_ne_zero, zero_pow two_ne_zero, one_pow, one_pow, add_zero,
      CharTwo.add_self_eq_zero]
  exact zero_ne_one (hinj e)

variable {K}

omit [Fintype K] in
theorem exists_root_cube_add_sq {K₃ : Type} [Field K₃] [Algebra K K₃] [Finite K₃]
    (h3 : Module.finrank K K₃ = 3) {c : K} (hc : ∀ t : K, t ^ 3 + t ^ 2 ≠ c) :
    ∃ θ : K₃, θ ^ 3 + θ ^ 2 + algebraMap K K₃ c = 0 := by
  set f : K[X] := X ^ 3 + X ^ 2 + C c with hf
  have hdeg : f.natDegree = 3 := by
    rw [hf]
    compute_degree!
  have hirr : Irreducible f := by
    refine irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) fun t ht => ?_
    apply hc t
    have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
    have ht' : t ^ 3 + t ^ 2 + c = 0 := by simpa [hf, Polynomial.IsRoot] using ht
    linear_combination ht' - c * h2K
  have : Fact (Irreducible f) := ⟨hirr⟩
  have hfin : Module.finrank K (AdjoinRoot f) = 3 := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := K) (K := AdjoinRoot f)
    (L := K₃) (by rw [hfin, h3])
  refine ⟨φ (AdjoinRoot.root f), ?_⟩
  have h := AdjoinRoot.aeval_algHom_eq_zero f φ
  simpa [hf] using h

end Cubic

section Coboundary

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {K₃ : Type} [Field K₃] [Algebra K K₃]
  [FiniteDimensional K K₃]

theorem exists_f4A2_orthogonal_coboundary (h3 : Module.finrank K K₃ = 3) (σ : K₃ ≃+* K₃)
    (hσ : ∀ b, σ b = b ^ Fintype.card K) (κ : F4A2Kind) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    ∃ P : Matrix.SpecialLinearGroup (Fin 3) K₃,
      ((f4A2Equiv K₃ κ ⟨_, weyl_word_mem_pair (M := K₃) κ ε⟩ :
        Matrix.SpecialLinearGroup (Fin 3) K₃) : Matrix (Fin 3) (Fin 3) K₃) =
          (P : Matrix (Fin 3) (Fin 3) K₃) * ((P : Matrix (Fin 3) (Fin 3) K₃).map σ)ᵀ := by
  have : CharP K₃ 2 := charP_of_injective_algebraMap (algebraMap K K₃).injective 2
  have : Finite K₃ := Module.finite_of_finite K
  obtain ⟨c, hc⟩ := exists_ne_cube_add_sq K
  obtain ⟨θ, hθ⟩ := exists_root_cube_add_sq h3 hc
  obtain ⟨-, -, -, -, hP⟩ :=
    EvenCubic.even_cubic_self_dual_basis_and_orthogonal_three_cycle_coboundary h3 σ hσ c hc θ hθ
  obtain ⟨π, hπ, hN⟩ := f4A2Equiv_weyl_word (M := K₃) κ hε
  have hperm : ∀ ρ : Equiv.Perm (Fin 3), (∀ a, ρ a = π a) → ρ.IsThreeCycle →
      ∃ P : Matrix.SpecialLinearGroup (Fin 3) K₃,
        ((f4A2Equiv K₃ κ ⟨_, weyl_word_mem_pair (M := K₃) κ ε⟩ :
          Matrix.SpecialLinearGroup (Fin 3) K₃) : Matrix (Fin 3) (Fin 3) K₃) =
            (P : Matrix (Fin 3) (Fin 3) K₃) * ((P : Matrix (Fin 3) (Fin 3) K₃).map σ)ᵀ := by
    intro ρ hρ hρ3
    obtain ⟨P, -, -, -, -, hPe⟩ := hP ρ hρ3
    refine ⟨P, ?_⟩
    rw [← hPe]
    ext a b
    rw [hN, Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, hρ]
    have hmem : (b ∈ some (π a)) ↔ b = π a := by rw [Option.mem_def, Option.some_inj, eq_comm]
    simp only [hmem]
    split_ifs <;> simp
  have h3c : (finRotate 3).IsThreeCycle := by
    rw [← card_support_eq_three_iff, support_finRotate]
    simp
  rcases hπ with rfl | rfl
  · refine hperm (finRotate 3)⁻¹ (fun a => ?_) h3c.inv
    rw [Equiv.Perm.inv_eq_iff_eq, finRotate_apply]
    fin_cases a <;> simp
  · refine hperm (finRotate 3) (fun a => ?_) h3c
    rw [finRotate_apply]
    fin_cases a <;> simp

end Coboundary

theorem map_map_eq_of_unitary {L : Type} [Field L] (σ : L ≃+* L)
    {B : Matrix (Fin 3) (Fin 3) L} (hB : (B.map σ)ᵀ * B = 1) : (B.map σ).map σ = B := by
  have h1 : B * (B.map σ)ᵀ = 1 := mul_eq_one_comm.1 hB
  have h2 : B.map σ * Bᵀ = 1 := by
    have := congrArg Matrix.transpose h1
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have h3 : ((B.map σ).map σ)ᵀ * B.map σ = 1 := by
    have := congrArg (RingEquiv.mapMatrix (m := Fin 3) σ) hB
    rwa [map_mul, map_one, RingEquiv.mapMatrix_apply, RingEquiv.mapMatrix_apply,
      Matrix.transpose_map] at this
  have h4 : ((B.map σ).map σ)ᵀ = Bᵀ := by
    calc ((B.map σ).map σ)ᵀ = ((B.map σ).map σ)ᵀ * (B.map σ * Bᵀ) := by
          rw [h2, Matrix.mul_one]
      _ = (((B.map σ).map σ)ᵀ * B.map σ) * Bᵀ := (Matrix.mul_assoc _ _ _).symm
      _ = Bᵀ := by rw [h3, Matrix.one_mul]
  exact Matrix.transpose_injective h4

end CFSG.RankThree.Chevalley
