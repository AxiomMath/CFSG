module

public import CFSG.Quasithin.Background.HSL3S77Model
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.Quasithin.H.S77

open Matrix

theorem sd_act (g : SL32) {x y : Vec} (h : SingDiag x y) : SingDiag (act g x) (dact g y) := by
  obtain ⟨hx, hy, hxy⟩ := h
  have hgg : ((g⁻¹ : SL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  refine ⟨fun h0 => hx ?_, fun h0 => hy ?_, ?_⟩
  · have := congrArg (fun v => ((g⁻¹ : SL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) h0
    rwa [act, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec, Matrix.mulVec_zero] at this
  · have := congrArg (fun v => (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ v) h0
    rwa [dact, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hgg, Matrix.transpose_one,
      Matrix.one_mulVec, Matrix.mulVec_zero] at this
  · rw [dact, act, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, Matrix.vecMul_vecMul, hgg,
      Matrix.vecMul_one]
    exact hxy

theorem sd_swap {x y : Vec} (h : SingDiag x y) : SingDiag y x :=
  ⟨h.2.1, h.1, by rw [dotProduct_comm]; exact h.2.2⟩

theorem sd_card : (Finset.univ.filter (fun q : Vec × Vec => SingDiag q.1 q.2)).card = 21 := by
  decide +kernel

theorem sd_trans' : ∀ x y : Vec, SingDiag x y →
    ∃ g : SL32, act g e1 = x ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ y = e3 := by
  decide +kernel

theorem sd_trans {x y : Vec} (h : SingDiag x y) : ∃ g : SL32, act g e1 = x ∧ dact g e3 = y := by
  obtain ⟨g, hg1, hg2⟩ := sd_trans' x y h
  refine ⟨g, hg1, ?_⟩
  have hinv : ((g⁻¹ : SL32) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]
  rw [dact, ← hg2, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]

end CFSG.Quasithin.H.S77
