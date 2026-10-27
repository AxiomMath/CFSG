module

public import CFSG.Quasithin.EmptyFaithful.S1421QA15Base

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421

variable {G : Type} [Group G] [Finite G]

structure Core3Ctx (T M H K1 L M₁ : Subgroup G) : Prop where
  st : Setting1427 T M H K1
  lt : sOf T K1 < T
  pCore_y : pCoreOf 2 (yOfL22 T M) ≤ sOf T K1
  pCore_ne : pCoreOf 2 (g0Of T M H K1) ≠ ⊥
  inM : InM (g0Of T M H K1) M₁
  not_le_T : ¬ T ≤ M₁
  sylow : IsSylowTwoOf (sOf T K1) M₁
  mem : L ∈ cComp (g0Of T M H K1)
  lt_L : K1 < L
  normal : (L.subgroupOf (g0Of T M H K1)).Normal
  eq : g0Of T M H K1 = L ⊔ yOfL22 T M ⊔ sOf T K1
  not_le_mc : ¬ L ≤ mcOf T

end S1421

@[expose] def Core3Quasi : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 L M₁ : Subgroup G),
    S1421.Core3Ctx T M H K1 L M₁ → ¬ CFSG.IsQuasisimple ↥L

@[expose] def Core3He : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 L M₁ : Subgroup G),
    S1421.Core3Ctx T M H K1 L M₁ → ¬ CFSG.IsQuasisimple ↥L →
      ¬ CharTwo (S1421.g0Of T M H K1)

end CFSG.Quasithin
