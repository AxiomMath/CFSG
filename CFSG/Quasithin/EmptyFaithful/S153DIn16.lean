module

public import CFSG.Quasithin.EmptyFaithful.S153DIn15
public import CFSG.Quasithin.EmptyFaithful.S153DC27

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

structure Ctx15313L {G : Type} [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G) :
    Prop where
  ctx : Ctx15313 T Mc M V₁ V₂ Yp I t
  facts : Facts15311 T M V₁ Yp I
  conc : Concl15315Two T M Yp I L

structure Concl15316 {G : Type} [Group G] [Finite G] (T M V₁ Yp I L : Subgroup G) : Prop where
  reduced_LR : IsTwoReducedIn (L ⊔ R153 T V₁ Yp) (WL153 T M L)
  reduced_LRY : IsTwoReducedIn (L ⊔ R153 T V₁ Yp ⊔ Yp) (WL153 T M L)
  quasi : CFSG.IsQuasisimple ↥(autOn L (WL153 T M L))
  YL_ne : YL153 Yp L ≠ ⊥
  R_norm : R153 T V₁ Yp ≤ Subgroup.normalizer (L : Set G)
  L_eq : ⁅L, thompsonJ (R153 T V₁ Yp)⁆ = L
  desc : C27Concl I (R153 T V₁ Yp) (M ⊓ I) L (omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp)))

@[expose] def Input15316One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15313L T Mc M V₁ V₂ Yp I L t →
    R153 T V₁ Yp ≤ Subgroup.normalizer (L : Set G) →
    pCoreOf 2 (L ⊔ R153 T V₁ Yp) ≤ R153 T V₁ Yp →
    C27Concl I (R153 T V₁ Yp) (M ⊓ I) L (omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp))) →
      IsTwoReducedIn (L ⊔ R153 T V₁ Yp) (WL153 T M L) ∧
        IsTwoReducedIn (L ⊔ R153 T V₁ Yp ⊔ Yp) (WL153 T M L)

end CFSG.Quasithin
