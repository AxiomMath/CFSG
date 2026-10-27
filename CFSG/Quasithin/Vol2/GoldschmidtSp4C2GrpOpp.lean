module

public import CFSG.Quasithin.Vol2.Ch3E213MP6BM

public section

namespace CFSG.Quasithin.Ch3E213M.Sp4C2

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp glMat uElt uMat glMat_uElt
  antiUnipotent)
open CFSG.Quasithin.SteinbergBS (glMat_mul_eq_of_conj mul_uMat_apply_zero mul_uMat_apply_one
  uMat_mul_apply_zero uMat_mul_apply_one uMat_mul_apply_two)
open CFSG.QuasithinUnique.Setup.X7b (uElt_zero_eq_one)

variable {k : Type} [Field k] [CharP k 2]

theorem eq_one_of_conj_mem {g : antiSp k} (hg : IsOppStd g) {x : antiSp k}
    (hx : x ∈ antiUnipotent k) (hx' : g⁻¹ * x * g ∈ antiUnipotent k) : x = 1 := by
  obtain ⟨a, b, c, d, rfl⟩ := hx
  obtain ⟨a', b', c', d', he⟩ := hx'
  have hE := glMat_mul_eq_of_conj he
  rw [glMat_uElt] at hE
  set G := glMat (g : GL (Fin 4) k) with hG
  obtain ⟨h30, hδ⟩ := hg
  rw [← hG] at h30 hδ
  have entry : ∀ (P Q : Matrix (Fin 4) (Fin 4) k), P = Q → ∀ i j, P i j = Q i j :=
    fun P Q h i j => by rw [h]
  have e20 := entry _ _ hE 2 0
  have e31 := entry _ _ hE 3 1
  have e10 := entry _ _ hE 1 0
  have e00 := entry _ _ hE 0 0
  have e11 := entry _ _ hE 1 1
  have e01 := entry _ _ hE 0 1
  rw [uMat_mul_apply_two, mul_uMat_apply_zero] at e20
  rw [P6B.uMat_mul_apply_three, mul_uMat_apply_one] at e31
  rw [uMat_mul_apply_one, mul_uMat_apply_zero] at e10
  rw [uMat_mul_apply_zero, mul_uMat_apply_zero] at e00
  rw [uMat_mul_apply_one, mul_uMat_apply_one] at e11
  rw [uMat_mul_apply_zero, mul_uMat_apply_one] at e01
  have ha : a = 0 :=
    (mul_eq_zero.mp (show a * G 3 0 = 0 by linear_combination e20)).resolve_right h30
  have ha' : a' = 0 :=
    (mul_eq_zero.mp (show G 3 0 * a' = 0 by linear_combination -e31)).resolve_left h30
  subst ha ha'
  have E0 : b * G 2 0 + c * G 3 0 = 0 := by linear_combination e00
  have E1 : b * G 2 1 + c * G 3 1 = 0 := by linear_combination e01
  have hb : b = 0 := by
    have : b * (G 2 0 * G 3 1 - G 2 1 * G 3 0) = 0 := by
      linear_combination G 3 1 * E0 - G 3 0 * E1
    exact (mul_eq_zero.mp this).resolve_right hδ
  have hc : c = 0 := by
    have : c * (G 2 0 * G 3 1 - G 2 1 * G 3 0) = 0 := by
      linear_combination G 2 0 * E1 - G 2 1 * E0
    exact (mul_eq_zero.mp this).resolve_right hδ
  subst hb hc
  have E2 : d * G 2 0 = 0 := by linear_combination e10
  have E3 : d * G 2 1 = 0 := by linear_combination e11
  have hd : d = 0 := by
    have : d * (G 2 0 * G 3 1 - G 2 1 * G 3 0) = 0 := by
      linear_combination G 3 1 * E2 - G 3 0 * E3
    exact (mul_eq_zero.mp this).resolve_right hδ
  subst hd
  exact uElt_zero_eq_one

end CFSG.Quasithin.Ch3E213M.Sp4C2
