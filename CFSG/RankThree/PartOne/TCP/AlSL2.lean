module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartOne.TCP

open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem commute_nilpotent_eq {N g : Matrix (Fin 2) (Fin 2) F}
    (hN2 : N * N = 0) (hN0 : N ≠ 0) (hg : g * N = N * g) :
    ∃ a b : F, g = a • (1 : Matrix (Fin 2) (Fin 2) F) + b • N := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, N = !![a, b; c, d] := ⟨_, _, _, _, Matrix.eta_fin_two N⟩
  obtain ⟨e, f, h, i, rfl⟩ : ∃ e f h i, g = !![e, f; h, i] := ⟨_, _, _, _, Matrix.eta_fin_two g⟩
  have h00 := congrFun (congrFun hN2 0) 0
  have h01 := congrFun (congrFun hN2 0) 1
  have h10 := congrFun (congrFun hN2 1) 0
  have h11 := congrFun (congrFun hN2 1) 1
  have g00 := congrFun (congrFun hg 0) 0
  have g01 := congrFun (congrFun hg 0) 1
  have g10 := congrFun (congrFun hg 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11 g00 g01 g10
  by_cases hc : c = 0
  · by_cases hb : b = 0
    · exfalso
      apply hN0
      have ha : a = 0 := by
        have : a * a = 0 := by rw [hc, hb] at h00; simpa using h00
        exact mul_self_eq_zero.mp this
      have hd : d = 0 := by
        have : d * d = 0 := by rw [hc, hb] at h11; simpa using h11
        exact mul_self_eq_zero.mp this
      rw [ha, hb, hc, hd]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · have ha : a = 0 := by
        have : a * a = 0 := by
          have : a * a + b * c = 0 := h00
          rw [hc] at this; simpa using this
        exact mul_self_eq_zero.mp this
      have hd : d = 0 := by
        have : d * d = 0 := by
          have : c * b + d * d = 0 := h11
          rw [hc] at this; simpa using this
        exact mul_self_eq_zero.mp this
      refine ⟨e, f / b, ?_⟩
      have hh : h = 0 := by
        have : f * c = b * h := by rw [ha] at g00; linear_combination g00
        rw [hc] at this
        have : b * h = 0 := by linear_combination -this
        exact (mul_eq_zero.mp this).resolve_left hb
      have hei : e = i := by
        have : e * b = b * i := by
          rw [ha, hd] at g01; linear_combination g01
        exact mul_right_cancel₀ hb (by linear_combination this)
      ext r s
      fin_cases r <;> fin_cases s
      · simp [ha]
      · simp [ha, hd]; field_simp
      · simp [hh, hc]
      · simp [hd, hei]
  · have hfc : f = h / c * b := by
      field_simp
      linear_combination g00
    have hie : i = e - h / c * a + h / c * d := by
      field_simp
      linear_combination g10
    refine ⟨e - h / c * a, h / c, ?_⟩
    ext r s
    fin_cases r <;> fin_cases s
    · simp
    · simp [hfc]
    · simp; field_simp
    · simp [hie]

@[expose] def sl2Upper : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def sl2Lower : SL(2, F) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩

theorem sl2Upper_sq [CharP F 2] : (sl2Upper : SL(2, F)) * sl2Upper = 1 := by
  have h11 : (1 : F) + 1 = 0 := by
    rw [one_add_one_eq_two]; exact_mod_cast CharP.cast_eq_zero F 2
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp [sl2Upper, h11, Matrix.one_fin_two]

theorem sl2Lower_sq [CharP F 2] : (sl2Lower : SL(2, F)) * sl2Lower = 1 := by
  have h11 : (1 : F) + 1 = 0 := by
    rw [one_add_one_eq_two]; exact_mod_cast CharP.cast_eq_zero F 2
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp [sl2Lower, h11, Matrix.one_fin_two]

theorem sl2_noncomm [CharP F 2] : (sl2Upper : SL(2, F)) * sl2Lower ≠ sl2Lower * sl2Upper := by
  intro h
  have h11 : (1 : F) + 1 = 0 := by
    rw [one_add_one_eq_two]; exact_mod_cast CharP.cast_eq_zero F 2
  have := congrArg (fun m : SL(2, F) => (m : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at this
  simp [sl2Upper, sl2Lower, Matrix.mul_apply, Fin.sum_univ_two, h11] at this

theorem eq_one_of_commute_noncomm [CharP F 2] {u v g : SL(2, F)} (hu : u * u = 1)
    (hv : v * v = 1) (huv : u * v ≠ v * u) (hgu : g * u = u * g) (hgv : g * v = v * g) :
    g = 1 := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have h2' : (2 : Matrix (Fin 2) (Fin 2) F) = 0 := by
    have : (2 : Matrix (Fin 2) (Fin 2) F) = ((2 : F) • (1 : Matrix (Fin 2) (Fin 2) F)) := by
      rw [two_smul]; norm_num
    rw [this, h2, zero_smul]
  set U : Matrix (Fin 2) (Fin 2) F := (u : Matrix (Fin 2) (Fin 2) F) with hU
  set V : Matrix (Fin 2) (Fin 2) F := (v : Matrix (Fin 2) (Fin 2) F) with hV
  set G : Matrix (Fin 2) (Fin 2) F := (g : Matrix (Fin 2) (Fin 2) F) with hG
  have hUU : U * U = 1 := by rw [hU]; exact_mod_cast congrArg Subtype.val hu
  have hVV : V * V = 1 := by rw [hV]; exact_mod_cast congrArg Subtype.val hv
  have hGU : G * U = U * G := congrArg Subtype.val hgu
  have hGV : G * V = V * G := congrArg Subtype.val hgv
  have hUV : U * V ≠ V * U := fun h => huv (Subtype.ext h)
  have hNN : (U - 1) * (U - 1) = 0 := by
    have : (U - 1) * (U - 1) = U * U - 2 * U + 1 := by noncomm_ring
    rw [this, hUU, h2', zero_mul, sub_zero, one_add_one_eq_two, h2']
  have hN0 : U - 1 ≠ 0 := by
    intro h
    have : U = 1 := sub_eq_zero.mp h
    apply hUV
    rw [this]; simp
  have hGN : G * (U - 1) = (U - 1) * G := by
    rw [mul_sub, sub_mul, hGU]; simp
  obtain ⟨a, b, hab⟩ := commute_nilpotent_eq hNN hN0 hGN
  have hGM : G * (V - 1) = (V - 1) * G := by
    rw [mul_sub, sub_mul, hGV]; simp
  have hb : b = 0 := by
    by_contra hb
    apply hUV
    rw [hab] at hGM
    have h3 : b • ((U - 1) * (V - 1)) = b • ((V - 1) * (U - 1)) := by
      have := hGM
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, one_mul,
        mul_one] at this
      exact add_left_cancel this
    have h4 := smul_right_injective _ hb h3
    calc U * V = (U - 1) * (V - 1) + U + V - 1 := by noncomm_ring
      _ = (V - 1) * (U - 1) + U + V - 1 := by rw [h4]
      _ = V * U := by noncomm_ring
  have hGa : G = a • (1 : Matrix (Fin 2) (Fin 2) F) := by rw [hab, hb]; simp
  have hdet : a ^ 2 = 1 := by
    have h1 : G.det = 1 := g.2
    rw [hGa, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h1
    exact h1
  have ha1 : a = 1 := by
    have h3 : (a - 1) ^ 2 = 0 := by
      have : (a - 1) ^ 2 = a ^ 2 - 2 * a + 1 := by ring
      rw [this, hdet, h2]
      linear_combination h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h3)
  exact Subtype.ext (hGa.trans (by rw [ha1, one_smul]; rfl))

end CFSG.RankThree.PartOne.TCP
