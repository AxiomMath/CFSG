module

public import CFSG.Quasithin.Vol2.Ch5Statements

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def A314FFFactE9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y T K KY V : Subgroup G), SQTKGroup ↥Y →
    IsSylowTwoOf T Y → K ≤ Y → K ∈ lFamily T → T ≤ Subgroup.normalizer (K : Set G) →
    Nonempty (O2Q K ≃* alternatingGroup (Fin 5)) →
    KY ∈ cComp Y → K < KY → Y ≤ Subgroup.normalizer (KY : Set G) →
    IsTwoReducedIn Y V → ¬ ⁅K, thompsonJ T⁆ ≤ Subgroup.centralizer (V : Set G) →
    (∃ a ∈ KY, ∃ b ∈ KY, a * b = b * a ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a ≠ 1 ∧
      b ∉ Subgroup.zpowers a) →
      IsSL3 4 (O2Q KY) ∨ IsPSp4 2 2 (O2Q KY) ∨ IsG2 2 2 (O2Q KY) ∨ IsAlt 7 ↥(autOn KY V)

end CFSG.Quasithin.H13.Ch9
