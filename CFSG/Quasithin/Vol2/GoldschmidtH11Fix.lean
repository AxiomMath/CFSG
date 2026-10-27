module

public import CFSG.Quasithin.Vol2.GoldschmidtH11Model

public section

open scoped Matrix MatrixGroups

namespace CFSG.Quasithin.H11

variable {F : Type} [Field F] [Finite F] [CharP F 2] (a : ℕ) (h : Nat.card F = 2 ^ (2 * a))

omit [Finite F] in
theorem tw_uSL (d : F) (M : Matrix (Fin 2) (Fin 2) F) :
    tw a (uSL d) M = !![M 0 0 + d * M 1 0 + (M 0 1 + d * M 1 1) * sg a d, M 0 1 + d * M 1 1;
      M 1 0 + M 1 1 * sg a d, M 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tw, coe_uSL, frobPow_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul,
      dotProduct]

omit [Finite F] in
theorem hm_eq (v : HV F a) :
    hm a v = !![hm a v 0 0, hm a v 0 1; sg a (hm a v 0 1), hm a v 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [(hm_entry a v 1 0).symm]

@[expose] noncomputable def hermV (x c y : F) (hx : sg a x = x) (hy : sg a y = y) : HV F a :=
  mkHV a !![x, c; sg a c, y] (by
    ext i j; fin_cases i <;> fin_cases j <;> simp [frobPow_apply, hx, hy, sg_sg a h])

theorem hm_hermV (x c y : F) (hx : sg a x = x) (hy : sg a y = y) :
    hm a (hermV a h x c y hx hy) = !![x, c; sg a c, y] := rfl

theorem actHom_uSL_fix_iff (v : HV F a) (d : F) :
    actHom a h (uSL d) v = v ↔
      d * hm a v 1 1 = 0 ∧ d * sg a (hm a v 0 1) + hm a v 0 1 * sg a d = 0 := by
  have hy := hm_entry a v 1 1
  have h10 := hm_entry a v 0 1
  have h01 : hm a v 1 0 = sg a (hm a v 0 1) := (hm_entry a v 1 0).symm
  rw [← hm_eq_iff, hm_actHom]
  change tw a (uSL d) (hm a v) = hm a v ↔ _
  rw [tw_uSL]
  constructor
  · intro hc
    have e01 := congrFun (congrFun hc 0) 1
    have e00 := congrFun (congrFun hc 0) 0
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at e01 e00
    have e1 : d * hm a v 1 1 = 0 := by linear_combination e01
    refine ⟨e1, ?_⟩
    rw [h01] at e00
    linear_combination e00 - sg a d * e1
  · rintro ⟨e1, e2⟩
    have e3 : hm a v 1 1 * sg a d = 0 := by
      have := congrArg (sg a) e1
      rw [map_mul, map_zero, hy] at this
      linear_combination this
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one]
    · rw [h01]; linear_combination e2 + sg a d * e1
    · linear_combination e1
    · linear_combination e3

theorem actHom_injective : Function.Injective (actHom a h : SL(2, F) →* MulAut (HV F a)) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  have hfix : ∀ v : HV F a, tw a z (hm a v) = hm a v := fun v => by
    have := congrArg (hm a) (DFunLike.congr_fun hz v)
    simpa [hm_actHom, tw] using this
  have e11 := hfix (hermV a h 1 0 0 (map_one _) (map_zero _))
  have e22 := hfix (hermV a h 0 0 1 (map_zero _) (map_one _))
  have eH := hfix (hermV a h 0 1 0 (map_zero _) (map_zero _))
  simp only [hm_hermV, tw] at e11 e22 eH
  have a1 := congrFun (congrFun e11 0) 0
  have a2 := congrFun (congrFun e11 1) 1
  have a3 := congrFun (congrFun e22 0) 0
  have a4 := congrFun (congrFun e22 1) 1
  have a5 := congrFun (congrFun eH 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, frobPow_apply] at a1 a2 a3 a4 a5
  have hdet := z.2
  rw [Matrix.det_fin_two, a2, a3] at hdet
  simp only [mul_zero, sub_zero] at hdet
  rw [a2, a3] at a5
  simp only [zero_add, map_zero, mul_zero] at a5
  have hp0 : (z : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have h1 : sg a ((z : Matrix (Fin 2) (Fin 2) F) 0 0) = sg a ((z : Matrix (Fin 2) (Fin 2) F) 1 1) :=
    mul_left_cancel₀ hp0 (a1.trans a5.symm)
  have h2 : (z : Matrix (Fin 2) (Fin 2) F) 0 0 = (z : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    simpa [sg_sg a h] using congrArg (sg a) h1
  have hp : (z : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    apply eq_one_of_mul_self_eq_one
    nth_rewrite 2 [h2]
    exact hdet
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a2, a3, hp, ← h2]

end CFSG.Quasithin.H11
