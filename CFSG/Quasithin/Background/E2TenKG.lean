module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.E2

open CFSG.Open

@[expose] def KGSz8CoverInvolutions : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → Subgroup.center K ≠ ⊥ →
    IsSz 3 (K ⧸ Subgroup.center K) →
    (∀ x : K ⧸ Subgroup.center K, orderOf x = 2 →
      ∃ y : K, orderOf y = 2 ∧ (y : K ⧸ Subgroup.center K) = x) ∧
    ∀ S : Sylow 2 K,
      (Subgroup.center ↥(S : Subgroup K)).map (S : Subgroup K).subtype = Subgroup.center K

end CFSG.Quasithin.E2
