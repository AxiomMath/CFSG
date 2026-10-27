module

public import CFSG.LocalAnalysis.StandardType.GGSL9TwoProj
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameNineTransfer
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB Multiplicative

theorem ggTorusOrderNineElt_ggSL9 :
    NbrFrameNine.GGTorusOrderNineElt 7 3 (GGSL9V ≃ₗ[ZMod 2] GGSL9V) := by
  intro E hE hr _
  obtain ⟨g, rfl⟩ := exists_conj_eq_ggSL9Torus hE hr
  refine ⟨3, (MulAut.conj g).toMonoidHom.comp ggSL9TorusCoord,
    (MulAut.conj g).injective.comp ggSL9TorusCoord_injective, ?_, g * ggSL9Shift * g⁻¹,
    ggSL9ShiftCoord, fun f => ?_, dvd_of_eq orderOf_ggSL9ShiftCoord.symm⟩
  · rw [MonoidHom.range_comp, range_ggSL9TorusCoord]
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← ggSL9Shift_conj_torusCoord f]
    group

theorem ggTorusOrderNine_ggSL9 :
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* (GGSL9V ≃ₗ[ZMod 2] GGSL9V))
      (A : Subgroup (MulAut L')),
      GGTorusTBGroup 7 3 (GGSL9V ≃ₗ[ZMod 2] GGSL9V)
        (Set.range (MulAut.conj :
          (GGSL9V ≃ₗ[ZMod 2] GGSL9V) →* MulAut (GGSL9V ≃ₗ[ZMod 2] GGSL9V))) L' ψ A →
        GGTorusOrderNine 7 A :=
  NbrFrameNine.ggTorusOrderNine_of_elt (by norm_num) subset_rfl center_ggSL9_eq_bot
    (ggCenterPrime_ggSL9 (by norm_num)) ggTorusOrderNineElt_ggSL9

theorem recipeLinear_frameNine {Q : LargeEvenRawCont} (h : LargeEvenRecipeLinear 9 2 Q) :
    LargeEvenRecipeLinear 9 2 fun R _ I F => Q R I F ∧ ∃ r, GGTorusLift 7 r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup 7 r R I L' ψ A → GGTorusOrderNine 7 A := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  refine ⟨K, inferInstance, inferInstance, hK, hQ, 3,
    TypeA.ggTorusLift_of_mulEquiv (ggSL9RecipeEquiv hK) ggTorusLift_ggSL9, ?_⟩
  intro L' _ _ ψ A hA
  exact ggTorusOrderNine_ggSL9 L' ((ggSL9RecipeEquiv hK).toMonoidHom.comp ψ) A
    (hA.mulEquiv (ggSL9RecipeEquiv hK) fun _ hφ => congr_ggSL9RecipeEquiv_mem hK hφ)

theorem ggNbrFrameNine_holds :
    LargeEvenLabelAll ⟨.A, 8, 1⟩ fun R _ I _ => ∃ r, GGTorusLift 7 r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup 7 r R I L' ψ A → GGTorusOrderNine 7 A :=
  fun _ hQ => recipeLinear_frameNine hQ

theorem ggNbrFrameInput_of_one (h : GGNbrFrameInputOne) : GGNbrFrameInput :=
  ⟨h, ggNbrFrameNine_holds⟩

end CFSG.StandardType

end
