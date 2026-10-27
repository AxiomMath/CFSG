module

public import CFSG.Quasithin.EmptyFaithful.S14612DA
public import CFSG.Quasithin.EmptyFaithful.S146F15
public import CFSG.Quasithin.EmptyFaithful.S146F21

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

@[expose] def A3AutFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X : Subgroup G), IsShort2 X → IsAltType X 3 →
    ∀ k : G, k ∈ Subgroup.normalizer (X : Set G) → orderOf k = 5 →
      k ∈ Subgroup.centralizer (X : Set G)

@[expose] def Input14615KzP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t → Ctx15 T M H p H₁ →
        ∀ (K₁ K₂ : Subgroup G) (s : G), Setup14615 T M H H₁ H₂ K₁ K₂ s →
          ¬ g2_14615 K₂ ≤ mcOf T →
            conjClosure (oTwoUpper H) (mcOf T) ≤ g2_14615 K₂ ∧
              conjClosure (oTwoUpper H) (mcOf T) ≤
                Subgroup.closure {x | x ∈ conjClosure (oTwoUpper H) (mcOf T) ∧ orderOf x = 5} ∧
              Subgroup.normalizer ((conjClosure (oTwoUpper H) (mcOf T) : Subgroup G) : Set G) ≤ mcOf T

end CFSG.Quasithin
