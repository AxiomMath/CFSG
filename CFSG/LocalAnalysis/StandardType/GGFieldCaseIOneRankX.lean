module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseIOneDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45RankXProper

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL45CyclicD4IOneInput_of_proper (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (h3 : GGNbrSubcomponentInput)
    (hR : GGL45D4BstarProperInput) : GGL45CyclicD4IOneInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hcfg hI1 hp3 hmk
  subst hp3
  exact hcfg.exists_cyclic_d4 hraw hiso (hcfg.card_bone_ge (hcfg.cent_le_of_iOne h3 hI1)
    (hcfg.pow_five_le_card_bstar (hR G 3 B Bs x L D J X B₂ d y K U U₁ hcfg rfl
      (largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h.1, h.2.1⟩) hmk)))) hmk

end CFSG.StandardType

end
