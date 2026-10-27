module

public import CFSG.Quasithin.Background.C126Defs

public section

namespace CFSG.Quasithin.C126

open CFSG.Open CFSG.QuasithinUnique B2F E2

@[expose] def RadFreeStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V : Subgroup G) (hV : IsElemAbelian 2 V),
    MinParabolic H T M → IsSQTKTC H → CharTwo H → IsTwoReducedIn H V → V = VZ T H →
    ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G) →
    (NatCase H T V hV ∨ A5Case H T V hV) →
    twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H

end CFSG.Quasithin.C126
