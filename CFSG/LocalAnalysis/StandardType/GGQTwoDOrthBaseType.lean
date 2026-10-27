module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthBase
public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMBridge
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBaseThm
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGQTwoPThree

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly

section Mono


theorem GGQTwoDRMBaseTypeInputOn.mono {R R' : ℕ → Prop} (h : GGQTwoDRMBaseTypeInputOn R)
    (hRR : ∀ m, R' m → R m) : GGQTwoDRMBaseTypeInputOn R' := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM
  exact h G p B Bs x L D J 𝒦 ι M e hcfg m e' (hRR m hm) hM

end Mono


theorem ggQTwoDRMBaseTypeInputOn_of_ne_six (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) :
    GGQTwoDRMBaseTypeInputOn fun m => 5 ≤ m ∧ m ≠ 6 := by
  classical
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM
  have hp : p = 3 := by
    obtain ⟨r, hr, hrc, h6⟩ := hcfg.2.2.2.2
    exact ggQTwo_p_eq_three hcfg.1 M e hcfg.2.2.2.1 hr hrc h6
  subst hp
  by_cases hL : qtwoOrthL G L 𝒦
  · exact Or.inr (ggQTwoDOrthBase_weylD ggLabelRigidInput_holds hTBF hWI hcfg e'
      (by omega) hM hL)
  · obtain ⟨F0, hF0, hF0fin, hF0char, ψ, ε, hbase⟩ :=
      ggQTwoDUnit_base_of_ne_six ggLabelRigidInput_holds hTBF hWI hcfg e' hm.1 hm.2 hM hL
    let _ : Field F0 := hF0
    have _ : Finite F0 := hF0fin
    have _ : CharP F0 2 := hF0char
    exact Or.inl (qtwoD_weylA_of_unitBase hbase (by omega))

theorem ggQTwoDRMBaseTypeInput_holds (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) :
    GGQTwoDRMBaseTypeInput :=
  (ggQTwoDRMBaseTypeInputOn_of_ne_six hTBF hWI).mono (R' := fun m => 7 ≤ m)
    fun m (hm : 7 ≤ m) => ⟨by omega, by omega⟩

end CFSG.StandardType.QTwo

end
