module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieSet
public import CFSG.LocalAnalysis.EvenBN.U5.Model
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieFld

public section

namespace CFSG.Quasithin.H13.F431.Un.OL5

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit CFSG.LocalAnalysis.EvenBN.U5
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

include hK in
theorem un5w_two : (2 : K) = 0 := by
  have := hK.charP
  exact_mod_cast CharP.cast_eq_zero K 2

theorem un5w_fieldP_conj_innM (σ : K ≃+* K) (g : hypSU hK 2 1) :
    fieldP hK σ * innM hK g * (fieldP hK σ)⁻¹ = innM hK (fieldAut hK σ g) := by
  have := aut5_mul_cj5_mul_inv hK (fieldP hK σ) (hypProj hK 2 1 g)
  rw [fieldP_apply] at this
  exact this

theorem un5w_fieldP_comm_innM (σ : K ≃+* K) {g : hypSU hK 2 1} (hg : fieldAut hK σ g = g) :
    fieldP hK σ * innM hK g = innM hK g * fieldP hK σ := by
  have := un5w_fieldP_conj_innM hK σ g
  rw [hg] at this
  exact mul_inv_eq_iff_eq_mul.1 this

theorem un5w_mat_fieldAut (σ : K ≃+* K) (g : hypSU hK 2 1) :
    mat (fieldAut hK σ g) = (mat g).map σ := rfl

theorem un5w_fieldAut_vSU (σ : K ≃+* K) {Y : Matrix (Fin 2) (Fin 2) K} (hY : IsHerm hK Y)
    (hσ : ∀ i j, σ (Y i j) = Y i j) : fieldAut hK σ (vSU hK Y hY) = vSU hK Y hY := by
  apply mat_injective
  rw [un5w_mat_fieldAut, mat_vSU hY]
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j <;>
    simp [oddUni, hσ, Matrix.one_apply, apply_ite σ]

theorem un5w_fieldAut_z₁SU (σ : K ≃+* K) : fieldAut hK σ (z₁SU hK) = z₁SU hK :=
  un5w_fieldAut_vSU hK σ _ (fun i j => by fin_cases i <;> fin_cases j <;> simp)

theorem un5w_det (s : K) : (!![1, s; 0, 1] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  simp [Matrix.det_fin_two]

theorem un5w_isUnit_det (s : K) : IsUnit (!![1, s; 0, 1] : Matrix (Fin 2) (Fin 2) K).det := by
  rw [un5w_det]
  exact isUnit_one

theorem un5w_mat_lev (s : K) :
    mat (lev (hK := hK) !![1, s; 0, 1] (un5w_isUnit_det s)) = oddDiag hK !![1, s; 0, 1] 1 := by
  rw [mat_lev, un5w_det]
  simp

theorem un5w_lev_mem (s : K) :
    lev (hK := hK) !![1, s; 0, 1] (un5w_isUnit_det s) ∈ hypUnitriangular hK 2 1 := by
  have h1 : (!![1, s; 0, 1] : Matrix (Fin 2) (Fin 2) K).IsUpperTriangular := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have h2 : ∀ i, (!![1, s; 0, 1] : Matrix (Fin 2) (Fin 2) K) i i = 1 := by
    intro i
    fin_cases i <;> simp
  have h3 : (0 : Matrix (Fin 2) (Fin 2) K) + ((0 : Matrix (Fin 2) (Fin 2) K).map hK.bar)ᵀ =
      -vecMulVec (0 : Fin 2 → K) (fun j => hK.bar ((0 : Fin 2 → K) j)) := by
    ext i j
    simp [vecMulVec]
  obtain ⟨g, hg, hgm⟩ := (exists_mem_hypUnitriangular_odd_iff (h := hK) (r := 2)
    (mat (lev (hK := hK) !![1, s; 0, 1] (un5w_isUnit_det s)))).2
    ⟨!![1, s; 0, 1], 0, 0, ⟨h1, h2⟩, h3, by rw [un5w_mat_lev, oddUni_zero, mul_one]⟩
  have : g = lev (hK := hK) !![1, s; 0, 1] (un5w_isUnit_det s) := mat_injective hgm
  rwa [this] at hg

theorem un5w_barInvT {s : K} (hs : hK.bar s = s) :
    barInvT hK (!![1, s; 0, 1] : Matrix (Fin 2) (Fin 2) K) = !![1, 0; s, 1] := by
  have hm : (!![1, s; 0, 1] : Matrix (Fin 2) (Fin 2) K).map hK.bar = !![1, s; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hs]
  have hinv : (!![1, s; 0, 1] : Matrix (Fin 2) (Fin 2) K)⁻¹ = !![1, -s; 0, 1] := by
    apply Matrix.inv_eq_right_inv
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have := hK.charP
  rw [barInvT, hm, hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq]

theorem un5w_fieldAut_lev {s : K} (hs : hK.bar s = s) :
    fieldAut hK (bar5 hK) (lev (hK := hK) !![1, s; 0, 1] (un5w_isUnit_det s)) =
      lev (hK := hK) !![1, s; 0, 1] (un5w_isUnit_det s) := by
  apply mat_injective
  rw [un5w_mat_fieldAut, un5w_mat_lev]
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j <;>
    simp [oddDiag, un5w_barInvT hK hs, fld5_bar_apply] <;>
    (fin_cases i <;> fin_cases j <;> simp [hs])

theorem un5w_isHerm {t : K} (ht : hK.bar t = t) :
    IsHerm hK (!![0, 0; 0, t] : Matrix (Fin 2) (Fin 2) K) := by
  rw [isHerm_iff]
  simp [ht]

theorem un5w_mat_comm {s t : K} (hs : hK.bar s = s) (ht : hK.bar t = t) :
    mat ⁅lev (hK := hK) !![1, s; 0, 1] (un5w_isUnit_det s),
        vSU hK !![0, 0; 0, t] (un5w_isHerm hK ht)⁆ =
      oddUni hK 0 !![s ^ 2 * t, s * t; s * t, 0] := by
  have hY := un5w_isHerm hK ht
  have h1 := lev_conj (hK := hK) !![1, s; 0, 1] (un5w_isUnit_det s) (mat_vSU hY)
  have h2 : (vSU hK !![0, 0; 0, t] hY)⁻¹ = vSU hK !![0, 0; 0, t] hY :=
    inv_eq_of_mul_eq_one_right (Vsub_sq (vSU_mem_Vsub hY))
  have hm : (!![1, s; 0, 1] : Matrix (Fin 2) (Fin 2) K).map hK.bar = !![1, s; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hs]
  have h3 := un5w_two hK
  rw [commutatorElement_def, mat_mul, h1, h2, mat_vSU hY, oddUni_mul]
  simp only [mulVec_zero, smul_zero, zero_add, hm]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_two, vecMulVec, Matrix.vecMul, dotProduct, Matrix.vecHead,
      Matrix.vecTail] <;> first | ring1 | linear_combination t * h3

theorem un5w_comm_prod {s₁ t₁ s₂ t₂ : K} (hs₁ : hK.bar s₁ = s₁) (ht₁ : hK.bar t₁ = t₁)
    (hs₂ : hK.bar s₂ = s₂) (ht₂ : hK.bar t₂ = t₂) (h1 : s₁ ^ 2 * t₁ + s₂ ^ 2 * t₂ = 1)
    (h2 : s₁ * t₁ + s₂ * t₂ = 0) :
    ⁅lev (hK := hK) !![1, s₁; 0, 1] (un5w_isUnit_det s₁),
        vSU hK !![0, 0; 0, t₁] (un5w_isHerm hK ht₁)⁆ *
      ⁅lev (hK := hK) !![1, s₂; 0, 1] (un5w_isUnit_det s₂),
        vSU hK !![0, 0; 0, t₂] (un5w_isHerm hK ht₂)⁆ = z₁SU hK := by
  apply mat_injective
  rw [mat_mul, un5w_mat_comm hK hs₁ ht₁, un5w_mat_comm hK hs₂ ht₂, oddUni_mul, z₁SU, mat_vSU]
  simp only [add_zero]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vecMulVec, h1, h2, Matrix.vecHead, Matrix.vecTail]

end CFSG.Quasithin.H13.F431.Un.OL5
