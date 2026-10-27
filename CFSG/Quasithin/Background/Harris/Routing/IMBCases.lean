module

public import CFSG.Quasithin.Background.Harris.Routing.Adapters
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case1M24
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case1M22
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case2
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case5HatA6

public section

namespace CFSG.Quasithin.G11.Harris

open CFSG.Open CFSG.Blueprint
open CFSG.Quasithin.Background.Harris.OrdinaryProofs

theorem oneCompFor_famSpor_M24 :
    OneCompFor (FamSpor .M24) :=
  oneCompFor_of_simple_quot (P := fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .M24))
    (fun _ _ _ _ e ⟨e'⟩ => ⟨e.trans e'⟩) (fun _ _ h => h)
    (fun _ _ _ _ _ _ _ _ hG hP => CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.case1_M24 hG hP)

theorem oneCompFor_famSpor_M22 :
    OneCompFor (FamSpor .M22) := by
  rintro V _ _ _ Γ A L m hs ⟨hsimp, ⟨e⟩⟩
  obtain ⟨e'⟩ := nonempty_quotCenterEquiv hs.L_comp hsimp
  exact CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.case1_M22 (OneCompSetting.toG93Hyp hs)
    (center_eq_bot_of_simple_component hs.L_comp hsimp) ⟨e'.trans e⟩

theorem oneCompFor_famHat_M22 :
    OneCompFor (FamHat (NativeSporadic.Carrier .M22)) := by
  rintro V _ _ _ Γ A L m hs ⟨hz, -, -, hM⟩
  exact CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.case2_HatM22 (OneCompSetting.toG93Hyp hs) hM hz

theorem oneCompFor_famHat_A6 :
    OneCompFor (FamHat (alternatingGroup (Fin 6))) := by
  rintro V _ _ _ Γ A L m hs ⟨hz, -, -, hM⟩
  exact CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.case5_hatA6 (OneCompSetting.toG93Hyp hs) hM hz

end CFSG.Quasithin.G11.Harris
