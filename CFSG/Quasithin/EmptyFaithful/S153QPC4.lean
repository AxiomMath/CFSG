module

public import CFSG.Quasithin.EmptyFaithful.S153QPA1
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismTransport

public section

namespace CFSG.Quasithin.QP

open Matrix Module CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
theorem exists_aut_map_stabilizer_of_finrank_one {W : Submodule F (Fin 3 → F)} (hW : finrank F W = 1) :
    ∃ θ : MulAut (SpecialLinearGroup (Fin 3) F),
      (stabilizer W).map (θ : SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F) =
        stabilizer (flagSpace 3 F 1) := by
  obtain ⟨h, hh⟩ := exists_map_flagSpace_eq W
  rw [hW] at hh
  refine ⟨MulAut.conj h⁻¹, ?_⟩
  have := stabilizer_map_conj h⁻¹ W
  refine this.trans ?_
  congr 1
  rw [← hh, ← Submodule.map_comp, ← mulVecLin_mul, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, mulVecLin_one, Submodule.map_id]

theorem exists_aut_map_eq_stabilizer_flag1 {P : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hP : IsMaxParabolic2 (⊤ : Subgroup (SpecialLinearGroup (Fin 3) F)) P) :
    ∃ θ : MulAut (SpecialLinearGroup (Fin 3) F),
      P.map (θ : SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F) =
        stabilizer (flagSpace 3 F 1) := by
  obtain ⟨g, d, hd1, hd3, hPd⟩ := exists_conj_stabilizer_of_isMaxParabolic2 (by norm_num : 1 ≤ 3) hP
  have hPW : P = stabilizer ((flagSpace 3 F d).map (mulVecLin (g : Matrix (Fin 3) (Fin 3) F))) := by
    rw [hPd, stabilizer_map_conj]
  have hfin : finrank F ((flagSpace 3 F d).map (mulVecLin (g : Matrix (Fin 3) (Fin 3) F))) = d := by
    exact (LinearEquiv.finrank_map_eq (SpecialLinearGroup.toLin' g) _).trans (finrank_flagSpace hd3.le)
  rcases (by omega : d = 1 ∨ d = 2) with rfl | rfl
  · rw [hPW]
    exact exists_aut_map_stabilizer_of_finrank_one hfin
  · set W := (flagSpace 3 F 2).map (mulVecLin (g : Matrix (Fin 3) (Fin 3) F)) with hW
    have hW' : finrank F (dotOrth W) = 1 := by
      rw [finrank_dotOrth, hfin]
    obtain ⟨θ₀, hθ₀⟩ := exists_aut_map_stabilizer_of_finrank_one hW'
    refine ⟨θ₀ * CatalogueBGraphForm.slGraphAut 3 F, ?_⟩
    have h1 := map_stabilizer_slGraphAut (n := 3) (K := F) W
    have e : ((θ₀ * CatalogueBGraphForm.slGraphAut 3 F : MulAut (SpecialLinearGroup (Fin 3) F)) :
        SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F) =
        (θ₀ : SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F).comp
          (CatalogueBGraphForm.slGraphAut 3 F : SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F) :=
      rfl
    rw [hPW, e, ← Subgroup.map_map, h1, hθ₀]

end CFSG.Quasithin.QP
