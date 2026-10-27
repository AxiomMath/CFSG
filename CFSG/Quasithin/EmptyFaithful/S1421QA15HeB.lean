module

public import CFSG.Quasithin.EmptyFaithful.S1421QA15Split

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Core3HeBorel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 L M₁ : Subgroup G),
    S1421.Core3Ctx T M H K1 L M₁ → CharTwo (S1421.g0Of T M H K1) →
      CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → yOfL22 T M ≤ L →
        yOfL22 T M ≤ Subgroup.normalizer ((S1421.sOf T K1 ⊓ L : Subgroup G) : Set G)

theorem core3HeSyl_of_borel (h : Core3HeBorel) : Core3HeSyl := by
  intro G _ _ T M H K1 L M₁ c hc hq hY
  have hYN := h G T M H K1 L M₁ c hc hq hY
  have hSG : S1421.sOf T K1 ≤ S1421.g0Of T M H K1 :=
    (le_sup_right : S1421.sOf T K1 ≤ yOfL22 T M ⊔ S1421.sOf T K1).trans
      (S1421.yOfL22_sup_sOf_le_g0Of T M H K1)
  have hSL : S1421.sOf T K1 ≤ Subgroup.normalizer (L : Set G) := hSG.trans c.g0Of_le_normalizer
  have hSS : S1421.sOf T K1 ≤ Subgroup.normalizer ((S1421.sOf T K1 ⊓ L : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer hSL).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hXN : yOfL22 T M ⊔ S1421.sOf T K1 ≤
      Subgroup.normalizer ((S1421.sOf T K1 ⊓ L : Subgroup G) : Set G) := sup_le hYN hSS
  have hR : S1421.sOf T K1 ⊓ L ≤ S1421.rOf T M K1 :=
    le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_right) hXN
      ((S1421.isPGroup_sOf c.st).to_le inf_le_left)
  have hsyl := A4.isSylowTwoOf_inf_normal (S1421.isSylowTwoOf_g0 c.inM c.sylow) c.le_g0Of
    c.g0Of_le_normalizer
  have heq : S1421.rOf T M K1 ⊓ L = S1421.sOf T K1 ⊓ L :=
    le_antisymm (inf_le_inf_right L (S1421.rOf_le_sOf c)) (le_inf hR inf_le_right)
  rw [heq]
  exact hsyl

end CFSG.Quasithin
