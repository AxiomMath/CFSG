module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandStructBasic

public section

namespace CFSG.StandardType

variable {G : Type} [Group G]

@[expose] def GGRCSSThreeSetting (G₀ : Subgroup G) (r : G) (Q S T : Subgroup G) : Prop :=
  G₀ ⊓ Subgroup.centralizer {r} ≤ ggRCSX G₀ r ∧ ggRCSX G₀ r = Q ⊔ (S ⊔ T) ∧ IsPGroup 2 Q ∧
    S ≤ Subgroup.normalizer (Q : Set G) ∧ T ≤ Subgroup.normalizer (Q : Set G) ∧
    S ≤ Subgroup.centralizer (T : Set G) ∧ Disjoint Q (S ⊔ T) ∧ Disjoint S T ∧
    ggRCSXd G₀ r = Q ⊔ T ∧ Nonempty (↥S ≃* Equiv.Perm (Fin 3)) ∧ CFSG.IsQuasisimple T ∧
    Subgroup.center ↥T = ⊥ ∧ 3 ∣ Nat.card T

@[expose] def GGRCSNbr (M : Subgroup G) (r : G) : Prop :=
  ∃ S₁ : Subgroup (GGRCSNbar r), GGRCSQuasiPiece 3 (ggRCSImg r M) S₁ ∧
    ∃ e : ↥(Subgroup.centralizer ({r} : Set G)), orderOf (e : G) = 3 ∧
      Subgroup.centralizer ({(e : G)} : Set G) ≤ M ∧ (QuotientGroup.mk e : GGRCSNbar r) ∈ S₁

end CFSG.StandardType
