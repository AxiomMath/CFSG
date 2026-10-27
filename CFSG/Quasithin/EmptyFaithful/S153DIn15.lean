module

public import CFSG.Quasithin.EmptyFaithful.S153DDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

@[expose] def Concl15315Two {G : Type} [Group G] [Finite G] (T M Yp I L : Subgroup G) : Prop :=
  L ∈ cComp (thompsonJ I) ∧ ¬ L ≤ M ⊓ I ∧ 1 ≤ CFSG.Open.pRank 3 L ∧ ⁅L, Yp⁆ = L ∧
    CFSG.IsQuasisimple ↥(autOn L (UI153 T I)) ∧ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)

@[expose] def Input15315Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I : Subgroup G) (t : G),
    Ctx15313 T Mc M V₁ V₂ Yp I t → Facts15311 T M V₁ Yp I →
      ∃ L : Subgroup G, L ∈ cComp (thompsonJ I) ∧ ¬ L ≤ M ⊓ I ∧ 1 ≤ CFSG.Open.pRank 3 L ∧
        CFSG.IsQuasisimple ↥(autOn L (UI153 T I)) ∧ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)

end CFSG.Quasithin
