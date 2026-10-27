module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMAt
public import CFSG.LocalAnalysis.StandardType.GGPsiInnerDiagOfMarking

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType

theorem rckRPConfigInnerDiag_holds :
    RCKRPConfigInnerDiag := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L K e h
  obtain ⟨hGG, -, -, -, -, -, -, -, hAnorm, hMarkG0, -⟩ := h
  exact ggPsiInnerDiag_of_marking hGG hMarkG0 hAnorm

end CFSG.StandardType.RCKRP
