module

public import CFSG.Quasithin.EmptyFaithful.S146Defs
public import CFSG.Quasithin.Background.F6Solvable
public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.EmptyFaithful.S145Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def Stage1466One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G), Setting146 G T M →
    IsHTM T M H → IsInvU T M H u → ∀ I : Subgroup G, IsIStar T M u I →
      T ⊓ I = tU T u ∨ T ⊓ I = tZero T u

@[expose] def Stage1466Six : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G), Setting146 G T M →
    IsHTM T M H → IsInvU T M H u → ∀ I : Subgroup G, IsIStar T M u I →
      2 ^ 9 < Nat.card T → yOfL22 T M = lI T M I ⊔ pCoreOf 2 (yOfL22 T M) →
      ∀ H₂ : Subgroup G, tZero T u ≤ H₂ →
        H₂ ≤ centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers u) →
        Nonempty (OTwoQuot H₂ ≃* Equiv.Perm (Fin 3)) → ¬ H₂ ≤ M →
        HasTwoNoncentralChiefFactors H₂ →
          IsIStar T M u ((lI T M I ⊔ (T ⊓ I)) ⊔ (oTwoUpper H₂ ⊔ (T ⊓ I))) ∧
            F6.IsGoldschmidtTripleIn ((lI T M I ⊔ (T ⊓ I)) ⊔ (oTwoUpper H₂ ⊔ (T ⊓ I)))
              (lI T M I ⊔ (T ⊓ I)) (oTwoUpper H₂ ⊔ (T ⊓ I))

@[expose] def Stage1469 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G), Setting146 G T M →
    IsHTM T M H → IsInvU T M H u → ∀ I : Subgroup G, IsIStar T M u I →
      4 < (pCoreOf 2 H).relIndex T →
      4 ≤ mIdx (conjClosure (VZ T M) H) (Subgroup.centralizer (pCoreOf 2 H : Set G)) →
        2 ^ 11 < Nat.card T ∧
          yOfL22 T M ⊔ T = (lI T M I ⊔ (T ⊓ I)) ⊔ pCoreOf 2 (yOfL22 T M ⊔ T)

@[expose] def Stage14610Five : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G), Setting146 G T M →
    IsHTM T M H → IsInvU T M H u → ∀ I : Subgroup G, IsIStar T M u I →
      4 < (pCoreOf 2 H).relIndex T →
      4 ≤ mIdx (conjClosure (VZ T M) H) (Subgroup.centralizer (pCoreOf 2 H : Set G)) →
      ∀ I₂ : Subgroup G, T ⊓ I ≤ I₂ → I₂ ≤ H → Nonempty (OTwoQuot I₂ ≃* Equiv.Perm (Fin 3)) →
        I = (lI T M I ⊔ (T ⊓ I)) ⊔ I₂ →
        (T ⊓ I = tU T u → I ≤ Subgroup.centralizer ({u} : Set G)) →
          Nat.card (conjClosure (VZ T M) I₂) = 2 ^ 3

end CFSG.Quasithin
