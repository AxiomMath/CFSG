module

public import CFSG.Quasithin.Vol2.Ch5Statements
public import CFSG.Quasithin.Background.A3Structure314Defs

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

@[expose] def A314InnerLieFact : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], SQTKHyp Y → ∀ T B L D : Subgroup Y,
    IsSylowTwoOf T ⊤ → B ∈ lFamily T → IsAlt 5 (ModO2 B) → L ∈ cComp ⊤ → B < L →
    A314Statement T B L → L.Normal → (IsSL3 4 ↥L ∨ IsPSp4 2 2 ↥L ∨ IsG2 2 2 ↥L) →
    IsPGroup 3 D → D ≤ L → (D : Set Y) * (T : Set Y) = (T : Set Y) * (D : Set Y) →
    T ≤ Subgroup.normalizer (B : Set Y) → D ≤ Subgroup.normalizer (B : Set Y)

@[expose] def A7FFNoA5Fact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y T K KY V : Subgroup G), SQTKGroup ↥Y →
    IsSylowTwoOf T Y → K ≤ KY → KY ≤ Y → Y ≤ Subgroup.normalizer (KY : Set G) →
    ⁅K, K⁆ = K → Nonempty (O2Q K ≃* alternatingGroup (Fin 5)) →
    T ≤ Subgroup.normalizer (K : Set G) → IsTwoReducedIn Y V → IsAlt 7 ↥(autOn KY V) →
    ¬ ⁅K, thompsonJ T⁆ ≤ Subgroup.centralizer (V : Set G) →
      ¬ K ≤ Subgroup.centralizer ((V ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) : Set G)

end CFSG.Quasithin.H13.Ch9
