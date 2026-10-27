module

public import CFSG.Quasithin.SteinbergBSSymplecticRoots
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear

public section

namespace CFSG.Quasithin.E2.TI2b.Sp4

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.Quasithin.SteinbergBS (rootLong rootShort)
open CFSG.LocalAnalysis.ComponentInitial (sl2Upper sl2Lower sl2_closure_upper_lower)
open scoped MatrixGroups

variable {k : Type} [Field k] [CharP k 2]

@[expose] def iotaMat (A : Matrix (Fin 2) (Fin 2) k) : Matrix (Fin 4) (Fin 4) k :=
  !![A 0 0, 0, 0, A 0 1; 0, 1, 0, 0; 0, 0, 1, 0; A 1 0, 0, 0, A 1 1]

theorem iotaMat_one : iotaMat (1 : Matrix (Fin 2) (Fin 2) k) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [iotaMat, Matrix.one_apply]

theorem iotaMat_mul (A B : Matrix (Fin 2) (Fin 2) k) :
    iotaMat (A * B) = iotaMat A * iotaMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [iotaMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four] <;> ring

theorem iotaMat_mem_of_det (B : Matrix (Fin 2) (Fin 2) k)
    (hdet : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1) :
    (iotaMat B)ᵀ * minorJ k * iotaMat B = minorJ k := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  ext i j
  rw [transpose_mul_minorJ_mul_apply]
  fin_cases i <;> fin_cases j <;> simp [iotaMat, minorJ_apply] <;>
    (first
      | ring1
      | linear_combination (B 0 0 * B 1 0) * h2
      | linear_combination (B 0 1 * B 1 1) * h2
      | linear_combination hdet + (B 0 1 * B 1 0) * h2)

theorem iotaMat_mem (A : SL(2, k)) :
    (iotaMat (A : Matrix (Fin 2) (Fin 2) k))ᵀ * minorJ k * iotaMat (A : Matrix (Fin 2) (Fin 2) k) =
      minorJ k := by
  apply iotaMat_mem_of_det
  have := Matrix.SpecialLinearGroup.det_coe A
  rw [Matrix.det_fin_two] at this
  exact this

theorem iotaMat_mul_inv (A : SL(2, k)) :
    iotaMat (A : Matrix (Fin 2) (Fin 2) k) *
      iotaMat ((A⁻¹ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = 1 := by
  rw [← iotaMat_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, iotaMat_one]

theorem iotaMat_inv_mul (A : SL(2, k)) :
    iotaMat ((A⁻¹ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) *
      iotaMat (A : Matrix (Fin 2) (Fin 2) k) = 1 := by
  rw [← iotaMat_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, iotaMat_one]

@[expose] noncomputable def iota : SL(2, k) →* antiSp k where
  toFun A := ⟨Units.mk (iotaMat (A : Matrix (Fin 2) (Fin 2) k))
      (iotaMat ((A⁻¹ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k))
      (iotaMat_mul_inv A) (iotaMat_inv_mul A), iotaMat_mem A⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    show iotaMat ((1 : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, iotaMat_one]
  map_mul' A B := by
    apply Subtype.ext
    apply Units.ext
    exact iotaMat_mul (A : Matrix (Fin 2) (Fin 2) k) (B : Matrix (Fin 2) (Fin 2) k)

theorem glMat_iota (A : SL(2, k)) :
    glMat ((iota A : antiSp k) : GL (Fin 4) k) = iotaMat (A : Matrix (Fin 2) (Fin 2) k) := rfl

theorem iotaMat_inj {A B : Matrix (Fin 2) (Fin 2) k} (h : iotaMat A = iotaMat B) : A = B := by
  have e00 : A 0 0 = B 0 0 := by simpa [iotaMat] using congrFun (congrFun h 0) 0
  have e01 : A 0 1 = B 0 1 := by simpa [iotaMat] using congrFun (congrFun h 0) 3
  have e10 : A 1 0 = B 1 0 := by simpa [iotaMat] using congrFun (congrFun h 3) 0
  have e11 : A 1 1 = B 1 1 := by simpa [iotaMat] using congrFun (congrFun h 3) 3
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11]

theorem iota_injective : Function.Injective (iota (k := k)) := by
  intro A B hAB
  have h : iotaMat (A : Matrix (Fin 2) (Fin 2) k) = iotaMat (B : Matrix (Fin 2) (Fin 2) k) := by
    rw [← glMat_iota, ← glMat_iota, hAB]
  exact Matrix.SpecialLinearGroup.ext _ _ fun i j => congrFun (congrFun (iotaMat_inj h) i) j

theorem iota_upper (c : k) : iota (sl2Upper k c) = uElt 0 0 c 0 := by
  apply antiSp_ext
  rw [glMat_iota, glMat_uElt]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [iotaMat, uMat, CFSG.LocalAnalysis.ComponentInitial.coe_sl2Upper]

theorem glMat_iota_lower (c : k) :
    glMat ((iota (sl2Lower k c) : antiSp k) : GL (Fin 4) k) = 1 + Matrix.single 3 0 c := by
  rw [glMat_iota]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [iotaMat, CFSG.LocalAnalysis.ComponentInitial.coe_sl2Lower, Matrix.single_apply]

theorem glMat_mul_antiSp (x y : antiSp k) :
    glMat ((x * y : antiSp k) : GL (Fin 4) k) =
      glMat (x : GL (Fin 4) k) * glMat (y : GL (Fin 4) k) :=
  rfl

theorem corner_matrix_comm (G : Matrix (Fin 4) (Fin 4) k) (t c : k)
    (h00 : G 0 0 = 0) (h10 : G 1 0 = 0) (h20 : G 2 0 = 0) (h30 : G 3 0 = t)
    (r0 : G 0 0 * t = 0) (r1 : G 0 1 * t = 0) (r2 : G 0 2 * t = 0) (r3 : G 0 3 * t = 1) :
    G * uMat 0 0 c 0 = (1 + Matrix.single 3 0 (c * t ^ 2)) * G := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, uMat, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply, -mul_eq_zero] <;>
    (first
      | ring1
      | linear_combination c * h00
      | linear_combination c * h10
      | linear_combination c * h20
      | linear_combination c * h30 + (-c * t) * r3
      | linear_combination -(c * h30) + (c * t) * r3
      | linear_combination (-c * t) * r0
      | linear_combination (-c * t) * r1
      | linear_combination (-c * t) * r2
      | linear_combination (c * t) * r0
      | linear_combination (c * t) * r1
      | linear_combination (c * t) * r2)

theorem exists_sl2_le_of_orbit {Y : Subgroup (antiSp k)} (hY : rootLong k ≤ Y) {y : antiSp k}
    (hy : y ∈ Y) (h30 : glMat (y : GL (Fin 4) k) 3 0 ≠ 0) :
    ∃ f : SL(2, k) →* antiSp k, Function.Injective f ∧ f.range ≤ Y ∧ rootLong k ≤ f.range := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  obtain ⟨t, ht⟩ : ∃ t : k, glMat (y : GL (Fin 4) k) 3 0 = t := ⟨_, rfl⟩
  have ht0 : t ≠ 0 := by rw [← ht]; exact h30
  obtain ⟨a, ha⟩ : ∃ a : k, a * t = glMat (y : GL (Fin 4) k) 2 0 :=
    ⟨glMat (y : GL (Fin 4) k) 2 0 / t, div_mul_cancel₀ _ ht0⟩
  obtain ⟨b, hb⟩ : ∃ b : k, b * t = glMat (y : GL (Fin 4) k) 1 0 :=
    ⟨glMat (y : GL (Fin 4) k) 1 0 / t, div_mul_cancel₀ _ ht0⟩
  obtain ⟨c₀, hc⟩ : ∃ c : k, c * t = glMat (y : GL (Fin 4) k) 0 0 :=
    ⟨glMat (y : GL (Fin 4) k) 0 0 / t, div_mul_cancel₀ _ ht0⟩
  obtain ⟨h, hh⟩ : ∃ h : antiSp k, h = uElt a b c₀ 0 := ⟨_, rfl⟩
  have hhU : h ∈ antiUnipotent k := by
    rw [hh]
    exact uElt_mem_antiUnipotent a b c₀ 0
  obtain ⟨g, hg⟩ : ∃ g : antiSp k, g = h⁻¹ * y := ⟨_, rfl⟩
  have hyg : y = h * g := by rw [hg, mul_inv_cancel_left]
  have hG : glMat (g : GL (Fin 4) k) =
      uMat a (b + a * 0) c₀ 0 * glMat (y : GL (Fin 4) k) := by
    subst hg hh
    rw [← glMat_uElt_inv]
    rfl
  have hG00 : glMat (g : GL (Fin 4) k) 0 0 = 0 := by
    rw [hG]
    simp [Matrix.mul_apply, Fin.sum_univ_four, uMat]
    linear_combination (-1 : k) * hc - a * hb - b * ha + c₀ * ht + (c₀ * t + a * b * t) * h2
  have hG10 : glMat (g : GL (Fin 4) k) 1 0 = 0 := by
    rw [hG]
    simp [Matrix.mul_apply, Fin.sum_univ_four, uMat]
    linear_combination (-1 : k) * hb + b * ht + (b * t) * h2
  have hG20 : glMat (g : GL (Fin 4) k) 2 0 = 0 := by
    rw [hG]
    simp [Matrix.mul_apply, Fin.sum_univ_four, uMat]
    linear_combination (-1 : k) * ha + a * ht + (a * t) * h2
  have hG30 : glMat (g : GL (Fin 4) k) 3 0 = t := by
    rw [hG]
    simp [Matrix.mul_apply, Fin.sum_univ_four, uMat]
    linear_combination ht
  have hsymp := mem_antiSp.mp g.2
  have hrow : ∀ j : Fin 4, glMat (g : GL (Fin 4) k) 0 j * t = minorJ k j 0 := by
    intro j
    have e := congrFun (congrFun hsymp j) 0
    rw [transpose_mul_minorJ_mul_apply, hG30, hG20, hG10, hG00] at e
    linear_combination e
  have r0 : glMat (g : GL (Fin 4) k) 0 0 * t = 0 := by
    rw [hrow 0]
    simp [minorJ_apply]
  have r1 : glMat (g : GL (Fin 4) k) 0 1 * t = 0 := by
    rw [hrow 1]
    simp [minorJ_apply]
  have r2 : glMat (g : GL (Fin 4) k) 0 2 * t = 0 := by
    rw [hrow 2]
    simp [minorJ_apply]
  have r3 : glMat (g : GL (Fin 4) k) 0 3 * t = 1 := by
    rw [hrow 3]
    simp [minorJ_apply]
  have hcomm : ∀ c : k, glMat (g : GL (Fin 4) k) * uMat 0 0 c 0 =
      (1 + Matrix.single 3 0 (c * t ^ 2)) * glMat (g : GL (Fin 4) k) :=
    fun c => corner_matrix_comm _ t c hG00 hG10 hG20 hG30 r0 r1 r2 r3
  have hcomm_rootLong : ∀ t' : k, h * uElt 0 0 t' 0 * h⁻¹ = uElt 0 0 t' 0 := by
    intro t'
    have hz : uElt 0 0 t' 0 ∈ antiUnipotentCenter k := ⟨0, t', rfl⟩
    have hzh := antiUnipotentCenter_comm hz hhU
    rw [← hzh, mul_inv_cancel_right]
  have hconj : ∀ μ : k, h * iota (sl2Lower k μ) * h⁻¹ ∈ Y := by
    intro μ
    obtain ⟨c, hcμ⟩ : ∃ c : k, c * t ^ 2 = μ :=
      ⟨μ / t ^ 2, div_mul_cancel₀ _ (pow_ne_zero 2 ht0)⟩
    have e1 : g * uElt 0 0 c 0 = iota (sl2Lower k μ) * g := by
      apply antiSp_ext
      rw [glMat_mul_antiSp, glMat_mul_antiSp, glMat_uElt, glMat_iota_lower, ← hcμ]
      exact hcomm c
    have hι : iota (sl2Lower k μ) = g * uElt 0 0 c 0 * g⁻¹ := by
      rw [e1, mul_inv_cancel_right]
    have hu : uElt 0 0 c 0 ∈ Y := hY ⟨c, rfl⟩
    have hconj_eq : h * iota (sl2Lower k μ) * h⁻¹ = y * uElt 0 0 c 0 * y⁻¹ := by
      rw [hι, hyg]
      group
    rw [hconj_eq]
    exact Y.mul_mem (Y.mul_mem hy hu) (Y.inv_mem hy)
  obtain ⟨f, hf⟩ : ∃ f : SL(2, k) →* antiSp k, ∀ A, f A = h * iota A * h⁻¹ :=
    ⟨(MulAut.conj h).toMonoidHom.comp iota, fun A => rfl⟩
  have hupper : ∀ c : k, f (sl2Upper k c) ∈ Y := fun c => by
    rw [hf, iota_upper, hcomm_rootLong c]
    exact hY ⟨c, rfl⟩
  have hlower : ∀ μ : k, f (sl2Lower k μ) ∈ Y := fun μ => by
    rw [hf]
    exact hconj μ
  have htop : (⊤ : Subgroup SL(2, k)) ≤ Y.comap f := by
    rw [← sl2_closure_upper_lower, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨μ, rfl⟩)
    · exact hupper c
    · exact hlower μ
  refine ⟨f, ?_, ?_, ?_⟩
  · intro A B hAB
    rw [hf, hf] at hAB
    exact iota_injective (mul_left_cancel (mul_right_cancel hAB))
  · intro x hx
    obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp hx
    exact Subgroup.mem_comap.mp (htop (Subgroup.mem_top A))
  · rintro u ⟨t', rfl⟩
    refine MonoidHom.mem_range.mpr ⟨sl2Upper k t', ?_⟩
    rw [hf, iota_upper, hcomm_rootLong t']

end CFSG.Quasithin.E2.TI2b.Sp4
