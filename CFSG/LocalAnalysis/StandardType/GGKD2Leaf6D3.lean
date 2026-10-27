module

public import CFSG.LocalAnalysis.StandardType.GGKD2Leaf6D3SimilitudeNorm
public import CFSG.LocalAnalysis.StandardType.GGKD2Leaf6D3UnitaryBlock
public import CFSG.LocalAnalysis.StandardType.GGKD2Leaf6D3LinearComponent
public import CFSG.LocalAnalysis.StandardType.GGKD2Leaf6D3UnitaryComponent
public import CFSG.LocalAnalysis.StandardType.GGKD2Leaf6D3LinearEndpoint
public import CFSG.LocalAnalysis.StandardType.GGKD2Leaf6D3UnitaryEndpoint

public section

namespace S2MathAs3_1624

noncomputable section

theorem unitaryComponentSimilitude_of (hN : UnitarySimilitudeNormalisation)
    (h : UnitaryComponentContract) : UnitaryComponentContractSimilitude := by
  intro K _ _ _ n hK d hd S κ hκ hS hS3 hSnorm J
  obtain ⟨c, κ', hSU, hS', hκ', hS'3, hproj⟩ := hN K n hK d hd S κ hκ hS hS3 hSnorm
  have key := h K n hK d hd _ κ' hκ' hSU hS'3 hS' J
  intro hJ
  exact key (by rw [← hproj]; exact hJ)

theorem d3Endpoints_of_jobs : LinearA1EightImpossible ∧ UnitaryA1EightForcesSixOne :=
  ⟨linearA1EightImpossible_of_component
      (linearComponent_of_blocks cubicFieldBlock_holds linearFullCentralizer_holds),
    unitaryA1EightForcesSixOne_of_component
      (unitaryComponentSimilitude_of unitarySimilitudeNormalisation_holds
        (unitaryComponent_of_block unitaryPrimaryBlock_holds))⟩

end

end S2MathAs3_1624

end
