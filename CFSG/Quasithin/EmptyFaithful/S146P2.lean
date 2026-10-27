module

public import CFSG.Quasithin.EmptyFaithful.S146F21
public import CFSG.Quasithin.EmptyFaithful.S14612DA
public import CFSG.Quasithin.EmptyFaithful.S146F15

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

@[expose] def Input14615SetupP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t → Ctx15 T M H p H₁ →
        ∃ (K₁ K₂ : Subgroup G) (s : G), Setup14615 T M H H₁ H₂ K₁ K₂ s

@[expose] def Input14615GP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t → Ctx15 T M H p H₁ →
        ∀ (K₁ K₂ : Subgroup G) (s : G), Setup14615 T M H H₁ H₂ K₁ K₂ s →
          ∀ (γ γ' : F8.Geom T (yOfL22 T M) H) (g : ↥(((yOfL22 T M) ⊔ T) ⊔ H)),
            F8Setup T (VZ T M) (yOfL22 T M) H γ γ' g →
              F8.A₁ (quasithinOmegaOneCenter T) (g : G) ≤ uHi T M H H₁ →
              quasithinOmegaOneCenter T ≤ conjSub (g : G) (uHi T M H H₁) →
              K₂ ≤ Subgroup.centralizer (F8.A₁ (quasithinOmegaOneCenter T) (g : G) : Set G) →
                (g : G) ∈ g2_14615 K₂

@[expose] def Input14615HypP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t → Ctx15 T M H p H₁ →
        ∀ (K₁ K₂ : Subgroup G) (s : G), Setup14615 T M H H₁ H₂ K₁ K₂ s →
          ¬ g2_14615 K₂ ≤ mcOf T →
            HypC23 (g2_14615 K₂) (pCoreOf 2 (mcOf T)) (g12_14615 T K₂) ∧ CharTwo (g2_14615 K₂) ∧
              ¬ oTwoFstarIn (g2_14615 K₂) ≤ g12_14615 T K₂

@[expose] def Input14615A3P : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t → Ctx15 T M H p H₁ →
        ∀ (K₁ K₂ : Subgroup G) (s : G), Setup14615 T M H H₁ H₂ K₁ K₂ s →
          ¬ g2_14615 K₂ ≤ mcOf T →
            ∀ X : Subgroup G, IsBlock2 (oTwoFIn (g2_14615 K₂)) X → IsAltType X 3 →
              X ≤ g12_14615 T K₂

@[expose] def Input14615JP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t → Ctx15 T M H p H₁ →
        ∀ (K₁ K₂ : Subgroup G) (s : G), Setup14615 T M H H₁ H₂ K₁ K₂ s →
          ¬ g2_14615 K₂ ≤ mcOf T →
            ∀ J : Subgroup G, J ∈ cComp (g2_14615 K₂) →
              CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) → ¬ J ≤ g12_14615 T K₂ →
                ⁅J, K₁⁆ = J ∧ pRank 5 J ≤ 1

@[expose] def Input14615ContraOuterP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t → Ctx15 T M H p H₁ →
        ∀ (K₁ K₂ : Subgroup G) (s : G), Setup14615 T M H H₁ H₂ K₁ K₂ s →
          ¬ g2_14615 K₂ ≤ mcOf T →
            ∀ J : Subgroup G, J ∈ cComp (g2_14615 K₂) →
              CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) → ¬ J ≤ g12_14615 T K₂ →
                ⁅J, K₁⁆ = J → pRank 5 J ≤ 1 → ¬ K₁ ≤ J → False

@[expose] def Input14615ContraInnerP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t → Ctx15 T M H p H₁ →
        ∀ (K₁ K₂ : Subgroup G) (s : G), Setup14615 T M H H₁ H₂ K₁ K₂ s →
          ¬ g2_14615 K₂ ≤ mcOf T →
            ∀ J : Subgroup G, J ∈ cComp (g2_14615 K₂) →
              CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) → ¬ J ≤ g12_14615 T K₂ →
                ⁅J, K₁⁆ = J → pRank 5 J ≤ 1 → K₁ ≤ J → False

end CFSG.Quasithin
