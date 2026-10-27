module

public import CFSG.Quasithin.EmptyFaithful.SBc17SL2Defs
import CFSG.Quasithin.Background.HOm4Aut

public section

namespace CFSG.Quasithin

namespace S153G93D

namespace SL2C

open SBc17

variable {F : Type} [Field F]

theorem coe_uElt (x : F) : (uElt x : Matrix (Fin 2) (Fin 2) F) = !![1, x; 0, 1] := rfl

theorem map_coe_uElt (τ : F ≃+* F) (t : F) :
    (uElt t : Matrix (Fin 2) (Fin 2) F).map τ = !![1, τ t; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_uElt]

theorem entries_of_mul_eq {M : Matrix (Fin 2) (Fin 2) F} {s t : F}
    (h : (uElt t : Matrix (Fin 2) (Fin 2) F) * M = M * !![1, s; 0, 1]) :
    t * M 1 0 = 0 ∧ t * M 1 1 = M 0 0 * s := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  simp only [coe_uElt, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one] at e00 e01
  constructor
  · linear_combination e00
  · linear_combination e01

theorem exists_smul_uElt_of_commute (τ : F ≃+* F) {M N : Matrix (Fin 2) (Fin 2) F}
    (hMN : M * N = 1) (hNM : N * M = 1)
    (key : ∀ t : F, (uElt t : Matrix (Fin 2) (Fin 2) F) * M = M * !![1, τ t; 0, 1]) :
    (∀ t : F, τ t = t) ∧ ∃ a e : F, a ≠ 0 ∧ M = a • (uElt e : Matrix (Fin 2) (Fin 2) F) ∧
      N = a⁻¹ • (((uElt e)⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨hc, hd'⟩ := entries_of_mul_eq (key 1)
  rw [map_one, one_mul, mul_one] at hd'
  rw [one_mul] at hc
  obtain ⟨a, ha_eq⟩ : ∃ a : F, M 0 0 = a := ⟨_, rfl⟩
  rw [ha_eq] at hd'
  have ha : a ≠ 0 := by
    intro h0
    have h11 := congrFun (congrFun hMN 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, hc, hd', h0] at h11
  have hτ : ∀ t : F, τ t = t := by
    intro t
    obtain ⟨-, h2⟩ := entries_of_mul_eq (key t)
    rw [hd', ha_eq] at h2
    exact mul_left_cancel₀ ha (by linear_combination (-1 : F) * h2)
  obtain ⟨e, he⟩ : ∃ e : F, M 0 1 = a * e := ⟨M 0 1 / a, by field_simp⟩
  have hMeq : M = a • (uElt e : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_uElt, hc, hd', ha_eq, he]
  have hY : (uElt e : Matrix (Fin 2) (Fin 2) F) *
      (((uElt e)⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h1 : M * (a⁻¹ • (((uElt e)⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F)) = 1 := by
    rw [hMeq, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ha, one_smul, hY]
  refine ⟨hτ, a, e, ha, hMeq, ?_⟩
  calc N = N * (M * (a⁻¹ • (((uElt e)⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F))) := by
        rw [h1, Matrix.mul_one]
    _ = (N * M) * (a⁻¹ • (((uElt e)⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F)) := by
        rw [Matrix.mul_assoc]
    _ = a⁻¹ • (((uElt e)⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) := by
        rw [hNM, Matrix.one_mul]

theorem exists_conj_uElt_of_fixes_upperSub [Finite F] [CharP F 2] (β : MulAut (SL2 F))
    (hβ : ∀ u ∈ upperSub F, β u = u) :
    ∃ e : F, ∀ g : SL2 F, β g = uElt e * g * (uElt e)⁻¹ := by
  obtain ⟨G, τ, hG⟩ := CFSG.Quasithin.H.Om4.exists_eq_conj_map β
  have hMN : (G : Matrix (Fin 2) (Fin 2) F) *
      ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hNM : ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (G : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  generalize (G : Matrix (Fin 2) (Fin 2) F) = M at hG hMN hNM
  generalize ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = N at hG hMN hNM
  have key : ∀ t : F, (uElt t : Matrix (Fin 2) (Fin 2) F) * M = M * !![1, τ t; 0, 1] := by
    intro t
    have h1 := hG (uElt t)
    rw [hβ (uElt t) (mem_upperSub_iff.2 ⟨t, rfl⟩), map_coe_uElt] at h1
    calc (uElt t : Matrix (Fin 2) (Fin 2) F) * M
        = (M * !![1, τ t; 0, 1] * N) * M := by rw [← h1]
      _ = M * !![1, τ t; 0, 1] := by rw [Matrix.mul_assoc, hNM, Matrix.mul_one]
  obtain ⟨hτ, a, e, ha, hMeq, hNeq⟩ := exists_smul_uElt_of_commute τ hMN hNM key
  refine ⟨e, fun g => ?_⟩
  have hmap : (g : Matrix (Fin 2) (Fin 2) F).map τ = (g : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    simp [Matrix.map_apply, hτ]
  apply Subtype.ext
  rw [hG g, hmap, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hNeq,
    hMeq]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ ha, one_smul]

end SL2C

end S153G93D

end CFSG.Quasithin
