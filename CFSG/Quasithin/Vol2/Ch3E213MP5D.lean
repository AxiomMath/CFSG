module

public import CFSG.Quasithin.Vol2.Ch3E213MP5A
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearAut
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import Certificates.Certificate113

public section

namespace CFSG.Quasithin.Ch3E213M.P5

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification

variable {k : Type} [Field k]

local notation "M3" => Matrix (Fin 3) (Fin 3) k

theorem coe_uu_one (t c : k) :
    ((uu t 0 c : Matrix.SpecialLinearGroup (Fin 3) k) : M3) =
      1 + (single 0 1 t + single 0 2 c) := by
  rw [coe_uu]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem coe_uu_two (t c : k) :
    ((uu 0 t c : Matrix.SpecialLinearGroup (Fin 3) k) : M3) =
      1 + (single 1 2 t + single 0 2 c) := by
  rw [coe_uu]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem coe_uu_one' (t : k) :
    ((uu t 0 0 : Matrix.SpecialLinearGroup (Fin 3) k) : M3) = 1 + single 0 1 t := by
  rw [coe_uu]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem coe_uu_two' (t : k) :
    ((uu 0 t 0 : Matrix.SpecialLinearGroup (Fin 3) k) : M3) = 1 + single 1 2 t := by
  rw [coe_uu]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem inv_transpose_uu_one (t : k) :
    (((uu t 0 0)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : M3)ᵀ = 1 + single 1 0 (-t) := by
  rw [uu_inv, coe_uu]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem inv_transpose_uu_two (t : k) :
    (((uu 0 t 0)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : M3)ᵀ = 1 + single 2 1 (-t) := by
  rw [uu_inv, coe_uu]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem conj_single_zero_one (a b : k) :
    ((uu b (-a) 0 : Matrix.SpecialLinearGroup (Fin 3) k) : M3) * single 0 1 1 *
      (((uu b (-a) 0)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : M3) =
        single 0 1 1 + single 0 2 a := by
  rw [uu_inv, coe_uu, coe_uu]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp

theorem conj_single_one_two (a b : k) :
    ((uu b (-a) 0 : Matrix.SpecialLinearGroup (Fin 3) k) : M3) * single 1 2 1 *
      (((uu b (-a) 0)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : M3) =
        single 1 2 1 + single 0 2 b := by
  rw [uu_inv, coe_uu, coe_uu]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp

theorem commute_of_conj_eq (A : GL (Fin 3) k) (u : Matrix.SpecialLinearGroup (Fin 3) k)
    {E Y : M3} (hA : (A : M3) * E * ((A⁻¹ : GL (Fin 3) k) : M3) = Y)
    (hu : (u : M3) * E * ((u⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : M3) = Y) :
    ((u⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : M3) * A * E =
      E * (((u⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : M3) * A) := by
  have hAinv := CFSG.QuasithinUnique.K1.coe_inv_mul_coe A
  have hu1 : ((u⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : M3) * (u : M3) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h1 : (A : M3) * E = Y * A := by
    rw [← hA, Matrix.mul_assoc _ _ (A : M3), hAinv, Matrix.mul_one]
  have h2 : ((u⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : M3) * Y =
      E * ((u⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : M3) := by
    rw [← hu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hu1, Matrix.one_mul]
  rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, h2, Matrix.mul_assoc]

theorem single_one_zero_mul :
    (single (1 : Fin 3) (0 : Fin 3) (-1 : k) * single (2 : Fin 3) (1 : Fin 3) (-1 : k) : M3) =
      0 := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp

theorem inner_of_fixes_mod_pzz [Finite k] [CharP k 2] (β : MulAut (projectiveSL 3 k))
    (hβ : ∀ u ∈ unitriangular 3 k, ∃ c : k, β (proj 3 k u) = proj 3 k (u * uu 0 0 c)) :
    ∃ x : projectiveSL 3 k, ∀ y, β y = x⁻¹ * y * x := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := k) (n := 3) le_rfl
  obtain ⟨A, σ, ε, hε, hβeq⟩ := hgen β
  have hdesc : descendAut 3 k (CFSG.QuasithinUnique.K1.stdAut A σ ε) = β := by
    rw [CFSG.QuasithinUnique.K1.descendAut_stdAut, ← hβeq]
  have hroot : ∀ a b : k, a * b = 0 →
      ∃ c : k, CFSG.QuasithinUnique.K1.stdAut A σ ε (uu a b 0) = uu a b c := by
    intro a b hab
    obtain ⟨c, hc⟩ := hβ _ (uu_mem_unitriangular a b 0)
    simp only [uu_mul, add_zero, zero_add, mul_zero] at hc
    rw [← hdesc, descendAut_proj] at hc
    refine ⟨c, CFSG.QuasithinUnique.K1.eq_of_proj_eq_of_mul_self_eq_one (by norm_num) ?_ ?_ hc⟩
    · rw [← map_mul, uu_mul_self, hab, uu_zero, map_one]
    · rw [uu_mul_self, hab, uu_zero]
  have hAinv := CFSG.QuasithinUnique.K1.coe_inv_mul_coe A
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  ·
    have hconj01 : ∀ t : k, ∃ c : k,
        (A : M3) * single 0 1 (σ t) * ((A⁻¹ : GL (Fin 3) k) : M3) =
          single 0 1 t + single 0 2 c := by
      intro t
      obtain ⟨c, hc⟩ := hroot t 0 (mul_zero t)
      have h := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) k => (g : M3)) hc
      rw [CFSG.QuasithinUnique.K1.coe_stdAut_zero, coe_uu_one',
        CFSG.QuasithinUnique.K1.map_one_add_single, coe_uu_one] at h
      exact ⟨c, CFSG.QuasithinUnique.K1.conj_eq_of_conj_one_add A h⟩
    obtain ⟨a, hE01⟩ := hconj01 1
    rw [map_one] at hE01
    have hσ : ∀ t, σ t = t := by
      intro t
      obtain ⟨c, h⟩ := hconj01 t
      have hs : (single (0 : Fin 3) (1 : Fin 3) (σ t) : M3) =
          σ t • (single (0 : Fin 3) (1 : Fin 3) (1 : k) : M3) := by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      rw [hs, Matrix.mul_smul, Matrix.smul_mul, hE01] at h
      have h01 := congrFun₂ h 0 1
      simpa using h01
    obtain rfl : σ = 1 := RingEquiv.ext hσ
    obtain ⟨b, hb⟩ := hroot 0 1 (zero_mul 1)
    have hE12 : (A : M3) * single 1 2 1 * ((A⁻¹ : GL (Fin 3) k) : M3) =
        single 1 2 1 + single 0 2 b := by
      have h := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) k => (g : M3)) hb
      rw [CFSG.QuasithinUnique.K1.coe_stdAut_zero, coe_uu_two',
        CFSG.QuasithinUnique.K1.map_one_add_single, map_one, coe_uu_two] at h
      exact CFSG.QuasithinUnique.K1.conj_eq_of_conj_one_add A h
    set u₁ : Matrix.SpecialLinearGroup (Fin 3) k := uu b (-a) 0 with hu₁
    have hc01 := commute_of_conj_eq A u₁ hE01 (conj_single_zero_one a b)
    have hc12 := commute_of_conj_eq A u₁ hE12 (conj_single_one_two a b)
    obtain ⟨α', β', hM⟩ := CFSG.QuasithinUnique.K1.eq_smul_one_add_single_of_commute (n := 3)
      (by norm_num) (((u₁⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : M3) * (A : M3)) (by
        intro i j hij
        fin_cases i <;> fin_cases j
        all_goals first | exact hc01 | exact hc12 | simp at hij)
    set A' : GL (Fin 3) k := (Matrix.SpecialLinearGroup.toGL u₁)⁻¹ * A with hA'
    have hA'coe : (A' : M3) = ((u₁⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : M3) * A := by
      rw [hA', Units.val_mul, ← map_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    have hα : α' ≠ 0 := by
      rintro rfl
      have hdet : IsUnit (A' : M3).det := (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit A')
      rw [hA'coe, hM, zero_smul, zero_add] at hdet
      simp [Matrix.det_fin_three] at hdet
    obtain ⟨x₀, hx₀⟩ := CFSG.QuasithinUnique.K1.exists_inner_of_matrix (n := 3) le_rfl A' hα
      (hA'coe.trans hM)
    refine ⟨x₀ * (proj 3 k u₁)⁻¹, fun y => ?_⟩
    obtain ⟨g, rfl⟩ := proj_surjective 3 k y
    have hstd : CFSG.QuasithinUnique.K1.stdAut A 1 0 =
        CatalogueBHigherLinearAction.slConjugation 3 k A := by
      simp [CFSG.QuasithinUnique.K1.stdAut]
    have hAeq : A = Matrix.SpecialLinearGroup.toGL u₁ * A' := by
      rw [hA', mul_inv_cancel_left]
    have h1 : ∀ h : Matrix.SpecialLinearGroup (Fin 3) k,
        CatalogueBHigherLinearAction.slConjugation 3 k (Matrix.SpecialLinearGroup.toGL u₁) h =
          u₁ * h * u₁⁻¹ := by
      intro h
      apply Matrix.SpecialLinearGroup.toGL_injective
      rw [CatalogueBHigherLinearAction.toGL_slConjugation, map_mul, map_mul, map_inv]
    have h2 := hx₀ (proj 3 k g)
    rw [descendAut_proj] at h2
    rw [← hdesc, descendAut_proj, hstd, hAeq, map_mul, MulAut.mul_apply, h1, map_mul, map_mul,
      map_inv, h2]
    group
  ·
    exfalso
    obtain ⟨c₁, hc₁⟩ := hroot 1 0 (mul_zero 1)
    obtain ⟨c₂, hc₂⟩ := hroot 0 1 (zero_mul 1)
    have e₁ : (A : M3) * single 1 0 (-1) * ((A⁻¹ : GL (Fin 3) k) : M3) =
        single 0 1 1 + single 0 2 c₁ := by
      have h := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) k => (g : M3)) hc₁
      rw [CFSG.QuasithinUnique.K1.coe_stdAut_one, inv_transpose_uu_one,
        CFSG.QuasithinUnique.K1.map_one_add_single, map_neg, map_one, coe_uu_one] at h
      exact CFSG.QuasithinUnique.K1.conj_eq_of_conj_one_add A h
    have e₂ : (A : M3) * single 2 1 (-1) * ((A⁻¹ : GL (Fin 3) k) : M3) =
        single 1 2 1 + single 0 2 c₂ := by
      have h := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) k => (g : M3)) hc₂
      rw [CFSG.QuasithinUnique.K1.coe_stdAut_one, inv_transpose_uu_two,
        CFSG.QuasithinUnique.K1.map_one_add_single, map_neg, map_one, coe_uu_two] at h
      exact CFSG.QuasithinUnique.K1.conj_eq_of_conj_one_add A h
    have hprod := CFSG.QuasithinUnique.K1.conj_mul_conj (A : M3) _ (single 1 0 (-1))
      (single 2 1 (-1)) hAinv
    rw [e₁, e₂, single_one_zero_mul, Matrix.mul_zero, Matrix.zero_mul] at hprod
    have h02 := congrFun₂ hprod 0 2
    simp only [Matrix.mul_apply, Fin.sum_univ_three] at h02
    simp at h02

end CFSG.Quasithin.Ch3E213M.P5
