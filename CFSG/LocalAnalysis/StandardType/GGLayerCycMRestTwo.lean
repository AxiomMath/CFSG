module

public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicRootCenter
public import CFSG.LocalAnalysis.StandardType.GGLayerCycMAdj
public import CFSG.LocalAnalysis.StandardType.GGLayerCycMInput
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess

public section

namespace CFSG.StandardType

open CFSG.Assembly

abbrev GGLieLayerInput : Prop :=
  GGLieLayerInputOn GGLieLayerLabel

section Reduction


theorem ggLayerCenterCyclicModelRestTwo_of_lieLayer (hG : CFSG.Open.GriessAllModelsStatement)
    (h : GGLieLayerInput) : GGLayerCenterCyclicModelRestTwo := by
  have hS : ∀ {S : LargeEvenLabel → Prop}, (∀ lab, S lab → GGLieLayerLabel lab) →
      GGLieLayerInputOn S := fun hS => h.mono hS
  refine ⟨⟨ggExcAdjLayerCycNonToralInput_G2_of_lieLayer hG (hS fun l hl => by
      simp [GGLieLayerLabel, hl]),
    ggExcAdjLayerCycNonToralInput_F4_of_lieLayer hG (hS fun l hl => by simp [GGLieLayerLabel, hl]),
    ggE6AdjLayerCycNonToralInput_of_lieLayer hG (hS fun l hl => by simp [GGLieLayerLabel, hl]),
    ggExcAdjLayerCycNonToralInput_E7_of_lieLayer hG (hS fun l hl => by simp [GGLieLayerLabel, hl]),
    ggExcAdjLayerCycNonToralInput_E8_of_lieLayer hG (hS fun l hl => by simp [GGLieLayerLabel, hl])⟩,
    fun p lab hp hp2 hlab hs hT => hT.elim
      (fun ht => ggLayerInnerModelOn_triD4_of_lieLayer hG
        (hS fun l hl => by simp [GGLieLayerLabel, hl]) p lab hp hp2 hlab hs ht)
      (fun ht => ggLayerInnerModelOn_twF4_of_lieLayer hG
        (hS fun l hl => by simp [GGLieLayerLabel, hl]) p lab hp hp2 hlab hs ht),
    ggLayerCenterCyclicExcSixRestInput_of_lieLayer hG (ggLieLayerInputOn_six_of_input h)⟩

end Reduction

section Final


theorem ggLayerCenterCyclicModelRestTwo_of_kfacts (h : GGLieLayerInput) :
    GGLayerCenterCyclicModelRestTwo :=
  ggLayerCenterCyclicModelRestTwo_of_lieLayer
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds h

end Final

end CFSG.StandardType

end
