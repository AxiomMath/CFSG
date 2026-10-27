module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDSelBasesFrame
public import CFSG.LocalAnalysis.StandardType.GGQTwoDSelModuleOfB2
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBaseThm

public section

namespace CFSG.StandardType.QTwo

section Final

theorem ggQTwoDUnitBaseInputOn_of_ne_six {R : ℕ → Prop} (hR : ∀ m, R m → 5 ≤ m ∧ m ≠ 6)
    (hRig : GGLabelRigidInput) (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) :
    GGQTwoDUnitBaseInputOn R := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM hL
  exact ggQTwoDUnit_base_of_ne_six hRig hTBF hWI hcfg e' (hR m hm).1 (hR m hm).2 hM hL

theorem ggQTwoLGenRankTwoInputOn_of_inputs {R : ℕ → Prop} (hR : ∀ m, R m → 5 ≤ m ∧ m ≠ 6)
    (hRig : GGLabelRigidInput) (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) :
    GGQTwoLGenRankTwoInputOn R :=
  ggQTwoLGenRankTwoInputOn_of_unitBase (fun m hm => by have := (hR m hm).1; omega)
    (ggQTwoDSelModuleInputOn_of_selectedModule (fun m hm => by have := (hR m hm).1; omega) hTBF
      hWI)
    (ggQTwoDUnitBaseInputOn_of_ne_six hR hRig hTBF hWI)

theorem ggQTwoLGenRankTwoInput_of_inputs (hRig : GGLabelRigidInput) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) : GGQTwoLGenRankTwoInput :=
  ggQTwoLGenRankTwoInputOn_of_inputs (R := fun m => 7 ≤ m) (fun m hm => ⟨by omega, by omega⟩)
    hRig hTBF hWI

end Final

end CFSG.StandardType.QTwo

end
