module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveTraceSplit
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveTraceAut

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

theorem exists_trace_form (R : SpecialLinearGroup (Fin 3) F4 →* SpecialLinearGroup (Fin 4) F4)
    (hR : Function.Injective R) :
    ∃ (σ : F4 ≃+* F4) (δ : Bool), ∀ s : SpecialLinearGroup (Fin 3) F4,
      Matrix.trace (R s : Matrix (Fin 4) (Fin 4) F4) =
        1 + σ (if δ then Matrix.trace ((s⁻¹ : SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)
          else Matrix.trace (s : Matrix (Fin 3) (Fin 3) F4)) := by
  obtain ⟨a, ha, h1⟩ := exists_trace_split R hR
  obtain ⟨σ, δ, h2⟩ := exists_trace_form_aut a ha
  exact ⟨σ, δ, fun s => by rw [h1, h2]⟩

end CFSG.StandardType.GGHalf

end
