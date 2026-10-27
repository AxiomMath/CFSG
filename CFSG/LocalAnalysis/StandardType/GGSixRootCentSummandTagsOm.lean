module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmPlus
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmMinus
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSU
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSpTwo
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandStructPSL

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.Assembly.LowTwoRank

section Tags

theorem ggRootCentSummandStructTag_POmegaMinus : GGRootCentSummandStructTag .POmegaMinus :=
  ggRootCentSummandStructTag_of_layerTag ggRootCentLayerTag_POmegaMinus

theorem ggRootCentSummandStructInput_of_excTags (hU5 : GGUFiveTwoRankInput)
    (hSp : GGSpSixEightRankInput) (hF4 : GGRootCentDerivedTag .F4)
    (hE6 : GGRootCentDerivedTag .E6) (hE7 : GGRootCentDerivedTag .E7)
    (hE8 : GGRootCentDerivedTag .E8) (hTwE6 : GGRootCentDerivedTag .twistedE6) :
    GGRootCentSummandStructInput := by
  refine ggRootCentSummandStructInput_of_tags fun t => ?_
  cases t with
  | PSL =>
    exact ggRootCentSummandStructTag_of_layerTag
      (ggRootCentLayerTag_of_derivedTag ggRootCentDerivedTag_PSL)
  | PSU =>
    exact ggRootCentSummandStructTag_of_layerTag
      (ggRootCentLayerTag_of_derivedTag (ggRootCentDerivedTag_PSU_of_rank hU5))
  | PSp => exact ggRootCentSummandStructTag_of_layerTag (ggRootCentLayerTag_PSp_of_rank hSp)
  | POmegaOdd => exact ggRootCentSummandStructTag_of_layerTag ggRootCentLayerTag_POmegaOdd
  | POmegaPlus => exact ggRootCentSummandStructTag_POmegaPlus
  | POmegaMinus => exact ggRootCentSummandStructTag_POmegaMinus
  | F4 => exact ggRootCentSummandStructTag_of_layerTag (ggRootCentLayerTag_of_derivedTag hF4)
  | E6 => exact ggRootCentSummandStructTag_of_layerTag (ggRootCentLayerTag_of_derivedTag hE6)
  | E7 => exact ggRootCentSummandStructTag_of_layerTag (ggRootCentLayerTag_of_derivedTag hE7)
  | E8 => exact ggRootCentSummandStructTag_of_layerTag (ggRootCentLayerTag_of_derivedTag hE8)
  | twistedE6 =>
    exact ggRootCentSummandStructTag_of_layerTag (ggRootCentLayerTag_of_derivedTag hTwE6)
  | G2 =>
    exact ggRootCentSummandStructTag_of_layerTag
      (ggRootCentLayerTag_of_placeholder _ (Or.inl rfl))
  | trialityD4 =>
    exact ggRootCentSummandStructTag_of_layerTag
      (ggRootCentLayerTag_of_placeholder _ (Or.inr (Or.inl rfl)))
  | twistedB2 =>
    exact ggRootCentSummandStructTag_of_layerTag
      (ggRootCentLayerTag_of_placeholder _ (Or.inr (Or.inr (Or.inl rfl))))
  | twistedG2 =>
    exact ggRootCentSummandStructTag_of_layerTag
      (ggRootCentLayerTag_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | twistedF4 =>
    exact ggRootCentSummandStructTag_of_layerTag
      (ggRootCentLayerTag_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  | Tits =>
    exact ggRootCentSummandStructTag_of_layerTag
      (ggRootCentLayerTag_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

end Tags

end CFSG.StandardType
