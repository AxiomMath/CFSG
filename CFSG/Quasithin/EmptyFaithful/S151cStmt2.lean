module

public import CFSG.Quasithin.EmptyFaithful.S151cStmt
public import CFSG.Quasithin.EmptyFaithful.S1515
public import CFSG.Quasithin.EmptyFaithful.S1516

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def StageLemma1515CE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M → Lemma1515Concl T Mc M

theorem stageLemma1515CE_of_description (hD : Description1512CE) : StageLemma1515CE := by
  intro G _ _ T Mc M h hM hCE
  exact lemma_15_1_5 h hM (hD G T Mc M h hM hCE)

@[expose] def StageLemma1516CE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M →
    oTwoUpper (M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤
      Subgroup.centralizer (V154 T Mc M : Set G)

theorem stageLemma1516CE_of (hnil : Nilpotency1512CE) : StageLemma1516CE := by
  intro G _ _ T Mc M h hM hCE
  exact lemma_15_1_6 h hM (hnil G T Mc M h hM hCE)

end CFSG.Quasithin
