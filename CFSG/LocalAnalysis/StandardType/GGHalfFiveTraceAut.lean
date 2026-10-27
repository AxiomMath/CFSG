module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveF4
public import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

theorem exists_trace_form_aut
    (a : SpecialLinearGroup (Fin 3) F4 →* SpecialLinearGroup (Fin 3) F4)
    (ha : Function.Injective a) :
    ∃ (σ : F4 ≃+* F4) (δ : Bool), ∀ s : SpecialLinearGroup (Fin 3) F4,
      Matrix.trace (a s : Matrix (Fin 3) (Fin 3) F4) =
        σ (if δ then Matrix.trace ((s⁻¹ : SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)
          else Matrix.trace (s : Matrix (Fin 3) (Fin 3) F4)) := by
  classical
  haveI : Finite (SpecialLinearGroup (Fin 3) F4) := inferInstance
  have hbij : Function.Bijective a := Finite.injective_iff_bijective.mp ha
  let β : MulAut (SpecialLinearGroup (Fin 3) F4) := MulEquiv.ofBijective a hbij
  have hβ : ∀ s : SpecialLinearGroup (Fin 3) F4,
      (β s : Matrix (Fin 3) (Fin 3) F4) = (a s : Matrix (Fin 3) (Fin 3) F4) :=
    fun s => congrArg (fun x : SpecialLinearGroup (Fin 3) F4 => (x : Matrix (Fin 3) (Fin 3) F4))
      (MulEquiv.ofBijective_apply a hbij s)
  obtain ⟨A, σ, h | h⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_matrix_form_of_mulAut_sl (n := 3) (K := F4) (by norm_num) β
  · refine ⟨σ, false, fun s => ?_⟩
    show Matrix.trace (a s : Matrix (Fin 3) (Fin 3) F4) =
      σ (Matrix.trace (s : Matrix (Fin 3) (Fin 3) F4))
    rw [← hβ s, h s, Matrix.trace_mul_cycle, Units.inv_mul, one_mul]
    exact (AddMonoidHom.map_trace σ (s : Matrix (Fin 3) (Fin 3) F4)).symm
  · refine ⟨σ, true, fun s => ?_⟩
    show Matrix.trace (a s : Matrix (Fin 3) (Fin 3) F4) =
      σ (Matrix.trace ((s⁻¹ : SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4))
    rw [← hβ s, h s, Matrix.trace_mul_cycle, Units.inv_mul, one_mul,
      ← AddMonoidHom.map_trace σ
        (((s⁻¹ : SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).transpose),
      Matrix.trace_transpose]

end CFSG.StandardType.GGHalf

end
