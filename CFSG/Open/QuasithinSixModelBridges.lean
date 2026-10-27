module

public import CFSG.Blueprint.Catalog
public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.Open.QuasithinSixModelsTauCeti

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley

@[expose] def TrialityD4ModelBridge : Prop :=
  ∀ (X : Type) [Group X], LieModel X .trialityD4 0 2 1 → Nonempty (X ≃* quasithinTrialityD4Two)

@[expose] def TitsModelBridge : Prop :=
  ∀ (X : Type) [Group X], LieModel X .Tits 0 2 1 → Nonempty (X ≃* quasithinTits)

end CFSG.Open.QuasithinSixModelsTauCeti
