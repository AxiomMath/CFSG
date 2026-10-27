module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthBase
public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitRMCoord
import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly


theorem ggQTwoDRMBaseCoordInput_holds (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) :
    GGQTwoDRMBaseCoordInput := by
  classical
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM
  by_cases hL : qtwoOrthL G L 𝒦
  · obtain ⟨hx, β₀, hjoin, i₀, c, hc, hβ, hstab⟩ := ggQTwoDOrthBase_coord
      ggLabelRigidInput_holds hTBF hWI hcfg e' (le_trans (by decide) hm) hM hL
    exact ⟨hx, β₀, hjoin, Or.inr ⟨i₀, c, hc, hβ, hstab⟩⟩
  · obtain ⟨hx, β₀, hjoin, ε, hε, hβ, hstab⟩ :=
      ggQTwoDUnit_rmBaseCoord ggLabelRigidInput_holds hTBF hWI hcfg e' hm hM hL
    exact ⟨hx, β₀, hjoin, Or.inl ⟨ε, hε, hβ, hstab⟩⟩

end CFSG.StandardType.QTwo

end
