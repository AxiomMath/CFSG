module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E8Five
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E8Large

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus Certificates.TcRes

theorem false_E8_four_of_inputs
    (hR : LangFamilyCompFieldSL) (hR2 : LangFamilyCompLabel) (hG6 : GGTCInputG6InnerDiagLang)
    {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}
    {ψ : (ggU .E8 n f).K →* X} (h : GGTCHyp .E8 n f ψ p G₀ B D J L x)
    (hF : GGSixLSevenFieldExtCase J .E8 f) (hc : orderOf ((2 : ZMod p) ^ f) = 4) :
    False := by
  by_cases hp : p = 5
  · exact false_E8_four_five_of_inputs hR hR2 hG6 h hF hc hp
  · exact false_E8_four_large_of_inputs hR hR2 hG6 h hF hc hp

end CFSG.StandardType.TableCRes

end
