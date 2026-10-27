module

public import CFSG.Quasithin.Background.SmithB45M22HatModel
public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin

open HatM22

@[expose] def HatM22SmallModules : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ L : Subgroup (MulAut V), IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22) →
      XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤ → Nat.card V < 2 ^ 30 →
        (FFModel.nat hatM22Γ₀).Realizes L ⊤ ⊥

end CFSG.Quasithin
