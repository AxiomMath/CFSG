module

public import CFSG.Quasithin.Background.SmithB45J2Zorn
public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.B4ModelsLie

public section

namespace CFSG.Quasithin

open J2Model

@[expose] def J2SmallModules : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ L : Subgroup (MulAut V), IsSporadic .J2 ↥L →
      XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤ → Nat.card V < 2 ^ 24 →
        (FFModel.zornQ j2Γ₀).Realizes L ⊤ ⊥

end CFSG.Quasithin
