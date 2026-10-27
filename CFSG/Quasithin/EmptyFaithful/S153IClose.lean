module

public import CFSG.Quasithin.EmptyFaithful.S153D43
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def Input15336OneCaseOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp : Subgroup G) (t : G),
    Hyp15310 G T Mc M V₁ V₂ Yp t → CFSG.Open.pRank 3 Yp = 2 → Yp = Y153 Mc M →
      ∀ I : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M I →
        ∃ φ : ↥(Yp ⊔ Sgp153 T V₁) →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3), Function.Surjective φ ∧
          φ.ker = (oTwoPhi (Yp ⊔ Sgp153 T V₁)).subgroupOf (Yp ⊔ Sgp153 T V₁)

@[expose] def Input15336OneCaseTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp : Subgroup G) (t : G),
    Hyp15310 G T Mc M V₁ V₂ Yp t → CFSG.Open.pRank 3 Yp = 2 →
      (IsUniqueM (Y153 Mc M ⊔ Sgp153 T V₁) M ∧
        Yp = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G))) →
      ∀ I : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M I →
        ∃ φ : ↥(Yp ⊔ Sgp153 T V₁) →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3), Function.Surjective φ ∧
          φ.ker = (oTwoPhi (Yp ⊔ Sgp153 T V₁)).subgroupOf (Yp ⊔ Sgp153 T V₁)

theorem input15336One_of_named_inputs (k1 : Input15336OneCaseOne) (k2 : Input15336OneCaseTwo) :
    Input15336One := by
  intro G _ _ T Mc M V₁ V₂ Yp t h hr I hI
  rcases h.cases with hY | h2
  · exact k1 G T Mc M V₁ V₂ Yp t h hr hY I hI
  · exact k2 G T Mc M V₁ V₂ Yp t h hr h2 I hI

@[expose] def Input15342 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          Lemma115LieCharTwo (↥L ⧸ Subgroup.center ↥L)

@[expose] def Input15335CloseLie : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          Lemma115LieCharTwo (↥L ⧸ Subgroup.center ↥L) → False

theorem input15335Close_of_named_inputs (k42 : Input15342) (kc : Input15335CloseLie) :
    Input15335Close := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL
  exact kc G T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL (k42 G T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL)

@[expose] def Input15343ElimLie : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp1 T Mc M V₁ V₂ Yp I L t → Concl15343Open T M V₁ V₂ Yp I L →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          Lemma115LieCharTwo (↥L ⧸ Subgroup.center ↥L) → False

@[expose] def Input15343ElimNonLie : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp1 T Mc M V₁ V₂ Yp I L t → Concl15343Open T M V₁ V₂ Yp I L →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          ¬ Lemma115LieCharTwo (↥L ⧸ Subgroup.center ↥L) → False

theorem input15343Elim_of_named_inputs (kL : Input15343ElimLie) (kN : Input15343ElimNonLie) :
    Input15343Elim := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c copen hmin hN hIeq hYL
  by_cases hLie : Lemma115LieCharTwo (↥L ⧸ Subgroup.center ↥L)
  · exact kL G T Mc M V₁ V₂ Yp I L t c copen hmin hN hIeq hYL hLie
  · exact kN G T Mc M V₁ V₂ Yp I L t c copen hmin hN hIeq hYL hLie

end CFSG.Quasithin
