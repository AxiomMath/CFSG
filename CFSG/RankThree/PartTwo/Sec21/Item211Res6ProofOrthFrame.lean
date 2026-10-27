module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofTau

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Res6Proof

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification
open Item211Lie2Proof Item211Res5Proof
open scoped MatrixGroups Matrix

section OrthFrame

variable {K : Type} [Field K]

@[expose] def frameMat (a b : K) : Matrix (Fin 3) (Fin 3) K := !![b, -a, 0; a, b, 1; a, b, -1]

theorem frameMat_mul_transpose {a b : K} (hab : a ^ 2 + b ^ 2 = -1) :
    frameMat a b * (frameMat a b)ᵀ = -jZero := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frameMat, jZero, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals first | ring1 | linear_combination hab

theorem det_frameMat {a b : K} (hab : a ^ 2 + b ^ 2 = -1) : (frameMat a b).det = 2 := by
  simp [frameMat, Matrix.det_fin_three]
  linear_combination (-2 : K) * hab

theorem exists_orthFrame {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) :
    ∃ P : GL (Fin 3) K, (P : Matrix (Fin 3) (Fin 3) K) * (P : Matrix (Fin 3) (Fin 3) K)ᵀ =
      -jZero ∧ ∀ σ : K ≃+* K, Matrix.GeneralLinearGroup.map (σ : K →+* K) P = P := by
  have hK2 : (2 : K) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp this)
  obtain ⟨a₀, b₀, hab₀⟩ := ZMod.sq_add_sq p (-1)
  set ι : ZMod p →+* K := ZMod.castHom (dvd_refl p) K with hι
  have hab : ι a₀ ^ 2 + ι b₀ ^ 2 = -1 := by
    rw [← map_pow, ← map_pow, ← map_add, hab₀]
    exact (map_neg ι 1).trans (congrArg Neg.neg (map_one ι))
  have hfix : ∀ (σ : K ≃+* K) (x : ZMod p), σ (ι x) = ι x := fun σ x => by
    have := RingHom.ext_zmod ((σ : K →+* K).comp ι) ι
    exact congrArg (fun φ : ZMod p →+* K => φ x) this
  have hdet : (frameMat (ι a₀) (ι b₀)).det ≠ 0 := by rw [det_frameMat hab]; exact hK2
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, frameMat_mul_transpose hab,
    fun σ => ?_⟩
  apply Units.ext
  change (frameMat (ι a₀) (ι b₀)).map σ = frameMat (ι a₀) (ι b₀)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frameMat, hfix]

theorem map_mOne (σ : K ≃+* K) : (mOne : Matrix (Fin 3) (Fin 3) K).map σ = mOne := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mOne, map_ofNat]

theorem map_mTwo (σ : K ≃+* K) : (mTwo : Matrix (Fin 3) (Fin 3) K).map σ = mTwo := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mTwo, map_ofNat]

variable {P : GL (Fin 3) K}

theorem fieldAut_conjAut_frame {σ : K ≃+* K}
    (hP : Matrix.GeneralLinearGroup.map (σ : K →+* K) P = P) {τ : SL(3, K)}
    (hτ : (τ : Matrix (Fin 3) (Fin 3) K).map σ = τ) :
    fieldAut 3 K σ (conjAut 3 K P⁻¹ (proj 3 K τ)) = conjAut 3 K P⁻¹ (proj 3 K τ) := by
  rw [← MulAut.mul_apply, fieldAut_mul_conjAut, MulAut.mul_apply, map_inv, hP, fieldAut_proj]
  congr 2
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  exact hτ

theorem dualAut_conjAut_frame
    (hP : (P : Matrix (Fin 3) (Fin 3) K) * (P : Matrix (Fin 3) (Fin 3) K)ᵀ = -jZero)
    {τ : SL(3, K)}
    (hτ : (τ : Matrix (Fin 3) (Fin 3) K) * jZero * (τ : Matrix (Fin 3) (Fin 3) K)ᵀ = jZero) :
    dualAut 3 K (conjAut 3 K P⁻¹ (proj 3 K τ)) = conjAut 3 K P⁻¹ (proj 3 K τ) := by
  rw [conjAut_proj, dualAut_proj]
  set X := CatalogueBHigherLinearAction.slConjugation 3 K P⁻¹ τ with hX
  obtain ⟨M, hM⟩ : ∃ M, M = (P : Matrix (Fin 3) (Fin 3) K) := ⟨_, rfl⟩
  obtain ⟨Mi, hMi⟩ : ∃ Mi, Mi = ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := ⟨_, rfl⟩
  have hMiM : Mi * M = 1 := by rw [hMi, hM, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hXm : (X : Matrix (Fin 3) (Fin 3) K) = Mi * τ * M := by
    rw [hX, coe_slConjugation, inv_inv, ← hMi, ← hM]
  have hXX : X * X.transpose = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_transpose,
      Matrix.SpecialLinearGroup.coe_one, hXm]
    rw [← hM] at hP
    calc Mi * (τ : Matrix (Fin 3) (Fin 3) K) * M * (Mi * (τ : Matrix (Fin 3) (Fin 3) K) * M)ᵀ =
        Mi * ((τ : Matrix (Fin 3) (Fin 3) K) * (M * Mᵀ) * (τ : Matrix (Fin 3) (Fin 3) K)ᵀ) *
          Miᵀ := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = -(Mi * jZero * Miᵀ) := by
          rw [hP, Matrix.mul_neg, Matrix.neg_mul, hτ, Matrix.mul_neg, Matrix.neg_mul]
      _ = (Mi * M) * (Mi * M)ᵀ := by
          rw [← neg_neg (jZero : Matrix (Fin 3) (Fin 3) K), ← hP, Matrix.transpose_mul]
          simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
      _ = 1 := by rw [hMiM, Matrix.transpose_one, Matrix.mul_one]
  have hinv : X⁻¹ = X.transpose := (eq_inv_of_mul_eq_one_right hXX).symm
  rw [hinv]
  congr 1

theorem fieldAut_dualAut_pow_frame
    (hP : (P : Matrix (Fin 3) (Fin 3) K) * (P : Matrix (Fin 3) (Fin 3) K)ᵀ = -jZero)
    (hPσ : ∀ σ : K ≃+* K, Matrix.GeneralLinearGroup.map (σ : K →+* K) P = P) {τ : SL(3, K)}
    (hτσ : ∀ σ : K ≃+* K, (τ : Matrix (Fin 3) (Fin 3) K).map σ = τ)
    (hτ : (τ : Matrix (Fin 3) (Fin 3) K) * jZero * (τ : Matrix (Fin 3) (Fin 3) K)ᵀ = jZero)
    (σ : K ≃+* K) (ε : ℕ) :
    (fieldAut 3 K σ * dualAut 3 K ^ ε) (conjAut 3 K P⁻¹ (proj 3 K τ)) =
      conjAut 3 K P⁻¹ (proj 3 K τ) := by
  have hδ : ∀ k : ℕ, (dualAut 3 K ^ k) (conjAut 3 K P⁻¹ (proj 3 K τ)) =
      conjAut 3 K P⁻¹ (proj 3 K τ) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, MulAut.mul_apply, dualAut_conjAut_frame hP hτ, ih]
  rw [MulAut.mul_apply, hδ, fieldAut_conjAut_frame (hPσ σ) (hτσ σ)]

end OrthFrame

end Item211Res6Proof

end CFSG.RankThree.PartTwo.Sec21
