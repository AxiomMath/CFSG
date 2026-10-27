module

public import CFSG.Quasithin.Background.Harris.Routing.Adapters
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case34A7
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case0M12

public section

namespace CFSG.Quasithin.G11.Harris

open CFSG.Open CFSG.Blueprint
open CFSG.Quasithin.Background.Harris.OrdinaryProofs

theorem oneCompFor_famAlt7 : OneCompFor (FamAlt 7) :=
  oneCompFor_of_simple_quot (P := fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7)))
    (fun _ _ _ _ e ⟨e'⟩ => ⟨e.trans e'⟩) (fun _ _ h => h)
    (fun _ _ _ _ _ _ _ _ hG hP =>
      CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.case34_A7 hG hP)

theorem oneCompFor_famHat_A7 : OneCompFor (FamHat (alternatingGroup (Fin 7))) := by
  rintro V _ _ _ Γ A L m hs ⟨-, -, -, hM⟩
  exact CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.case34_A7
    (OneCompSetting.toG93Hyp hs) hM

theorem oneCompFor_famSpor_M12 :
    OneCompFor (FamSpor .M12) :=
  oneCompFor_of_simple_quot (P := fun X _ => Nonempty (X ≃* NativeSporadic.Carrier .M12))
    (fun _ _ _ _ e ⟨e'⟩ => ⟨e.trans e'⟩) (fun _ _ h => h)
    (fun _ _ _ _ _ _ _ _ hG hP =>
      CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.case0_M12_concl hG hP)

end CFSG.Quasithin.G11.Harris
