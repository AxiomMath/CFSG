module

public import CFSG.Milestones.ASVolI.C4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped commutatorElement Pointwise

@[expose] def burnsideC41b_ClauseBridgeN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V K : Subgroup G), HypC41 H R M L V K →
    R ≤ Subgroup.normalizer (K : Set G) → CFSG.Quasithin.C41Case3 H R M L V K →
    C134CorrLocal.IsC134Case4Corr (K ⊔ R) R K → IsC134Case 4 (K ⊔ R) R K

end CFSG.ASVolI
