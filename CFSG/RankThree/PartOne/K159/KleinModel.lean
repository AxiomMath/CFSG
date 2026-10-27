module

public import CFSG.LocalAnalysis.SteinbergCEPfaffianFour
public import CFSG.LieType.Universal.Spin.Forms
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public section

namespace CFSG.RankThree.PartOne.K159.Klein

open Matrix CFSG.LocalAnalysis CFSG.LieType.Universal.Spin

variable {K : Type*} [Field K]

@[expose] def alt (v : Fin 3 ⊕ Fin 3 → K) : Matrix (Fin 4) (Fin 4) K :=
  antiMat (v (.inl 0)) (v (.inl 1)) (v (.inl 2)) (v (.inr 2)) (v (.inr 1)) (v (.inr 0))

@[expose] def coords (M : Matrix (Fin 4) (Fin 4) K) : Fin 3 ⊕ Fin 3 → K :=
  Sum.elim ![M 0 1, M 0 2, M 0 3] ![M 2 3, M 1 3, M 1 2]

theorem coords_alt (v : Fin 3 ⊕ Fin 3 → K) : coords (alt v) = v := by
  funext s
  rcases s with i | i <;> fin_cases i <;> simp [coords, alt, antiMat]

theorem alt_add (v w : Fin 3 ⊕ Fin 3 → K) : alt (v + w) = alt v + alt w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [alt, antiMat] <;> ring

theorem alt_smul (c : K) (v : Fin 3 ⊕ Fin 3 → K) : alt (c • v) = c • alt v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [alt, antiMat]

theorem coords_add (M N : Matrix (Fin 4) (Fin 4) K) : coords (M + N) = coords M + coords N := by
  funext s
  rcases s with i | i <;> fin_cases i <;> simp [coords]

theorem coords_smul (c : K) (M : Matrix (Fin 4) (Fin 4) K) : coords (c • M) = c • coords M := by
  funext s
  rcases s with i | i <;> fin_cases i <;> simp [coords]

@[expose] def altL : (Fin 3 ⊕ Fin 3 → K) →ₗ[K] Matrix (Fin 4) (Fin 4) K where
  toFun := alt
  map_add' := alt_add
  map_smul' := alt_smul

@[expose] def coordsL : Matrix (Fin 4) (Fin 4) K →ₗ[K] (Fin 3 ⊕ Fin 3 → K) where
  toFun := coords
  map_add' := coords_add
  map_smul' := coords_smul

@[expose] def cong (g : Matrix (Fin 4) (Fin 4) K) :
    (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K) :=
  coordsL ∘ₗ ((LinearMap.mulRight K gᵀ) ∘ₗ (LinearMap.mulLeft K g)) ∘ₗ altL

theorem cong_apply (g : Matrix (Fin 4) (Fin 4) K) (v : Fin 3 ⊕ Fin 3 → K) :
    cong g v = coords (g * alt v * gᵀ) := rfl

section CharTwo

variable [CharP K 2]

theorem alt_transpose (v : Fin 3 ⊕ Fin 3 → K) : (alt v)ᵀ = alt v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [alt, antiMat, CharTwo.neg_eq]

theorem alt_coords (M : Matrix (Fin 4) (Fin 4) K) (hM : Mᵀ = M) (hd : ∀ i, M i i = 0) :
    alt (coords M) = M := by
  have hs : ∀ i j, M j i = M i j := fun i j => by
    have := congrFun (congrFun hM i) j
    simpa using this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [alt, coords, antiMat, CharTwo.neg_eq, hd] <;>
    exact hs _ _

theorem cong_symm (g : Matrix (Fin 4) (Fin 4) K) (v : Fin 3 ⊕ Fin 3 → K) :
    (g * alt v * gᵀ)ᵀ = g * alt v * gᵀ := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, alt_transpose,
    Matrix.mul_assoc]

omit [CharP K 2] in
theorem cong_diag (g : Matrix (Fin 4) (Fin 4) K) (v : Fin 3 ⊕ Fin 3 → K) (i : Fin 4) :
    (g * alt v * gᵀ) i i = 0 :=
  congr_antiMat_apply_self g _ _ _ _ _ _ i

theorem alt_cong (g : Matrix (Fin 4) (Fin 4) K) (v : Fin 3 ⊕ Fin 3 → K) :
    alt (cong g v) = g * alt v * gᵀ :=
  alt_coords _ (cong_symm g v) (cong_diag g v)

theorem cong_mul (g h : Matrix (Fin 4) (Fin 4) K) (v : Fin 3 ⊕ Fin 3 → K) :
    cong (g * h) v = cong g (cong h v) := by
  rw [cong_apply g (cong h v), alt_cong, cong_apply (g * h) v, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

omit [CharP K 2] in
theorem cong_one (v : Fin 3 ⊕ Fin 3 → K) : cong 1 v = v := by
  rw [cong_apply, Matrix.transpose_one]
  simp [coords_alt]

theorem quadPlus_eq_pfS_alt (v : Fin 3 ⊕ Fin 3 → K) : quadPlus 3 K v = pfS (alt v) := by
  rw [quadPlus_apply, Fin.sum_univ_three]
  simp [pfS, alt, antiMat, sub_eq_add_neg, CharTwo.neg_eq]

theorem quadPlus_cong (g : Matrix (Fin 4) (Fin 4) K) (hg : g.det = 1) (v : Fin 3 ⊕ Fin 3 → K) :
    quadPlus 3 K (cong g v) = quadPlus 3 K v := by
  rw [quadPlus_eq_pfS_alt, quadPlus_eq_pfS_alt, alt_cong]
  have h := pfS_congr g (v (.inl 0)) (v (.inl 1)) (v (.inl 2)) (v (.inr 2)) (v (.inr 1))
    (v (.inr 0))
  rw [hg, one_mul] at h
  exact h

theorem cong_coe_mul (g h : SpecialLinearGroup (Fin 4) K) (v : Fin 3 ⊕ Fin 3 → K) :
    cong ((g * h : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) v =
      cong (g : Matrix (Fin 4) (Fin 4) K) (cong (h : Matrix (Fin 4) (Fin 4) K) v) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, cong_mul]

@[expose] noncomputable def rho :
    SpecialLinearGroup (Fin 4) K →* ((Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) where
  toFun g := LinearEquiv.ofLinearMap (cong (g : Matrix (Fin 4) (Fin 4) K))
    (cong ((g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, ← cong_coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, cong_one]
      rfl)
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, ← cong_coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, cong_one]
      rfl)
  map_one' := LinearEquiv.ext fun v => by
    rw [LinearEquiv.coe_ofLinearMap, Matrix.SpecialLinearGroup.coe_one, cong_one]
    rfl
  map_mul' g h := LinearEquiv.ext fun v => by
    rw [LinearEquiv.coe_ofLinearMap, cong_coe_mul]
    rfl

theorem rho_apply (g : SpecialLinearGroup (Fin 4) K) (v : Fin 3 ⊕ Fin 3 → K) :
    rho g v = cong (g : Matrix (Fin 4) (Fin 4) K) v := rfl

theorem rho_mem (g : SpecialLinearGroup (Fin 4) K) :
    rho g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  rw [rho_apply]
  exact quadPlus_cong _ g.2 v

end CharTwo

end CFSG.RankThree.PartOne.K159.Klein
