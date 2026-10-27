module

public import CFSG.LocalAnalysis.StandardType.GGHalfLeviGlue
public import CFSG.LocalAnalysis.StandardType.GGHalfStageADefs
public import CFSG.LocalAnalysis.StandardType.GGFieldNbr

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

theorem ggTypeAHalfCoord_of_levi (hsub : GGNbrSubcomponentInput) (h : GGTypeAHalfLeviInput) :
    GGTypeAHalfCoordInput := by
  intro G _ _ p B Bs x L D J m y K hcfg hInn hN
  have hJK : J ≤ K := hsub G p B x L D J hcfg.1 hcfg.2.2 y K hN.2.2.2.2.1
  obtain ⟨ψ₁, ψ₂, hdata⟩ := h G p B Bs x L D J m y K hcfg hInn hN hJK
  exact ggHalfCoords_of_leviData (by have := hN.2.2.1; omega) hdata

end CFSG.StandardType

end
