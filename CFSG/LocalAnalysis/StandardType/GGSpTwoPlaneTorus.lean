module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeSp

public section

namespace CFSG.StandardType

namespace TwoThree

open CFSG.LieType.SteinbergBR.EvenSp Matrix

private theorem permMatrix_conj {n R : Type*} [Fintype n] [DecidableEq n] [Field R]
    (σ : Equiv.Perm n) (A : Matrix n n R) :
    Equiv.Perm.permMatrix R σ * A * Equiv.Perm.permMatrix R σ.symm =
      A.submatrix σ σ := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, Equiv.Perm.permMatrix,
    PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix]
  rfl

section

variable {K : Type} [Field K] {r : ℕ}

private theorem swapGL_mul_self : swapGL (K := K) * swapGL = 1 := by
  apply Units.ext
  change !![(0 : K), 1; 1, 0] * !![0, 1; 1, 0] = 1
  rw [Matrix.mul_fin_two, Matrix.one_fin_two]
  simp

@[expose] noncomputable def planePermGL : Equiv.Perm (Fin r) →* GL (Fin r ⊕ Fin r) K :=
  ((Matrix.permMatrixHom : Equiv.Perm (Fin r ⊕ Fin r) →* Matrix _ _ K).toHomUnits).comp
    ((Equiv.Perm.sumCongrHom (Fin r) (Fin r)).comp ((MonoidHom.id _).prod (MonoidHom.id _)))

private theorem planePermGL_val (σ : Equiv.Perm (Fin r)) :
    ((planePermGL (K := K) σ : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      Equiv.Perm.permMatrix K (Equiv.Perm.sumCongr σ σ).symm := by
  rfl

private theorem planeMat_submatrix_sumCongr (σ : Equiv.Perm (Fin r))
    (g : Fin r → Matrix (Fin 2) (Fin 2) K) :
    (planeMat g).submatrix (Equiv.Perm.sumCongr σ σ).symm (Equiv.Perm.sumCongr σ σ).symm =
      planeMat (g ∘ σ.symm) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [planeMat, Matrix.submatrix_apply, Matrix.diagonal_apply, Equiv.sumCongr_apply]

private theorem planePermGL_conj (σ : Equiv.Perm (Fin r)) (g : Fin r → GL (Fin 2) K) :
    planePermGL (K := K) σ * planeHom g * (planePermGL (K := K) σ)⁻¹ =
      planeHom (g ∘ σ.symm) := by
  apply Units.ext
  change ((planePermGL (K := K) σ : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((planeHom g : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      (((planePermGL (K := K) σ)⁻¹ : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
    ((planeHom (g ∘ σ.symm) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
  have hInv : (((planePermGL (K := K) σ)⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      Equiv.Perm.permMatrix K (Equiv.Perm.sumCongr σ σ) := by
    rw [← map_inv, planePermGL_val]
    simp [Equiv.symm_symm, Equiv.Perm.inv_def]
  rw [planePermGL_val, planeHom_val, planeHom_val, hInv]
  have hconj := permMatrix_conj (Equiv.Perm.sumCongr σ σ).symm
    (planeMat fun j => (g j : Matrix (Fin 2) (Fin 2) K))
  simp only [Equiv.symm_symm] at hconj
  rw [hconj]
  exact planeMat_submatrix_sumCongr σ fun j => (g j : Matrix (Fin 2) (Fin 2) K)

end

variable {K : Type} [Field K] [CharP K 2] {r : ℕ}

private theorem planeGram_submatrix_sumCongr (σ : Equiv.Perm (Fin r)) :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).submatrix
        (Equiv.Perm.sumCongr σ σ) (Equiv.Perm.sumCongr σ σ) =
      fromBlocks 0 1 (-1) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.submatrix_apply, Equiv.sumCongr_apply, Matrix.one_apply, CharTwo.neg_eq]

private theorem det_swapGL :
    ((swapGL (K := K) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  change (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K).det = 1
  rw [Matrix.det_fin_two_of, zero_mul, one_mul, zero_sub, CharTwo.neg_eq]

private theorem swapGL_conj_tPow (a : Multiplicative (ZMod 3)) :
    swapGL (K := K) * tPow a * swapGL⁻¹ = (tPow a)⁻¹ := by
  rw [tPow, TableBSymp.zmodPowHom_apply, ← inv_pow, ← conj_pow, swapGL_conj_tGL]

@[expose] noncomputable def spPlaneTorus :
    (Fin r → Multiplicative (ZMod 3)) →* CFSG.Open.StatedSp r K :=
  (planeHom.comp (MonoidHom.compLeft (tPow (K := K)) (Fin r))).codRestrict _ fun f =>
    planeHom_mem_statedSp _ fun j =>
      det_of_mem_zpowers (TableBSymp.zmodPowHom_mem (t := tGL (K := K)) tGL_pow_three
        (Subgroup.mem_zpowers _) (f j))

@[expose] noncomputable def planeInv (k : Fin r) : CFSG.Open.StatedSp r K :=
  ⟨planeHom (Pi.mulSingle k swapGL), by
    apply planeHom_mem_statedSp
    intro j
    by_cases hj : j = k
    · subst hj
      rw [Pi.mulSingle_eq_same]
      exact det_swapGL
    · rw [Pi.mulSingle_eq_of_ne hj]
      exact Matrix.det_one⟩

theorem planePermGL_mem (σ : Equiv.Perm (Fin r)) :
    planePermGL (K := K) σ ∈ CFSG.Open.StatedSp r K := by
  rw [mem_statedSp_iff']
  have hP := planePermGL_val (K := K) (r := r) σ
  have hPt : ((planePermGL (K := K) σ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ =
      Equiv.Perm.permMatrix K (Equiv.Perm.sumCongr σ σ) := by
    rw [hP]
    simp [Equiv.symm_symm, Equiv.Perm.inv_def]
  rw [hPt, hP, permMatrix_conj]
  exact planeGram_submatrix_sumCongr σ

@[expose] noncomputable def planePerm : Equiv.Perm (Fin r) →* CFSG.Open.StatedSp r K :=
  planePermGL.codRestrict _ planePermGL_mem

theorem spPlaneTorus_injective : Function.Injective (spPlaneTorus (K := K) (r := r)) := by
  intro f g hfg
  have h1 : planeHom (fun j => tPow (f j)) = planeHom (fun j => tPow (g j)) :=
    congrArg (fun x : CFSG.Open.StatedSp r K => (x : GL (Fin r ⊕ Fin r) K)) hfg
  have h2 := planeHom_injective h1
  funext j
  exact tPow_injective (K := K) (congrFun h2 j)

theorem planeInv_mul_self (k : Fin r) : planeInv (K := K) k * planeInv k = 1 := by
  apply Subtype.ext
  change (planeHom (Pi.mulSingle k (swapGL (K := K))) *
      planeHom (Pi.mulSingle k (swapGL (K := K))) : GL (Fin r ⊕ Fin r) K) = 1
  rw [← map_mul, ← Pi.mulSingle_mul, swapGL_mul_self, Pi.mulSingle_one, map_one]

theorem planeInv_conj_spPlaneTorus (k : Fin r) (f : Fin r → Multiplicative (ZMod 3)) :
    planeInv (K := K) k * spPlaneTorus f * (planeInv k)⁻¹ =
      spPlaneTorus (Function.update f k (f k)⁻¹) := by
  apply Subtype.ext
  change (planeHom (Pi.mulSingle k (swapGL (K := K))) *
      planeHom (fun j => tPow (f j)) *
      (planeHom (Pi.mulSingle k (swapGL (K := K))))⁻¹ : GL (Fin r ⊕ Fin r) K) =
    planeHom (fun j => tPow (Function.update f k (f k)⁻¹ j))
  have hfun : (Pi.mulSingle k (swapGL (K := K)) : Fin r → GL (Fin 2) K) *
      (fun j => tPow (f j)) *
      (Pi.mulSingle k (swapGL (K := K)) : Fin r → GL (Fin 2) K)⁻¹ =
      fun j => tPow (Function.update f k (f k)⁻¹ j) := by
    funext j
    by_cases hj : j = k
    · subst hj
      rw [Pi.mul_apply, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.inv_apply,
        Pi.mulSingle_eq_same, Function.update_self, swapGL_conj_tPow, ← map_inv]
      rfl
    · rw [Pi.mul_apply, Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, Pi.inv_apply,
        Pi.mulSingle_eq_of_ne hj, one_mul, inv_one, mul_one, Function.update_of_ne hj]
  rw [← map_mul, ← map_inv, ← map_mul, hfun]

theorem planePerm_conj_spPlaneTorus (σ : Equiv.Perm (Fin r))
    (f : Fin r → Multiplicative (ZMod 3)) :
    planePerm (K := K) σ * spPlaneTorus f * (planePerm σ)⁻¹ = spPlaneTorus (f ∘ σ.symm) := by
  apply Subtype.ext
  change (planePermGL (K := K) σ * planeHom (fun j => tPow (f j)) *
      (planePermGL (K := K) σ)⁻¹ : GL (Fin r ⊕ Fin r) K) =
    planeHom (fun j => tPow ((f ∘ σ.symm) j))
  rw [planePermGL_conj]
  rfl

end TwoThree

end CFSG.StandardType
