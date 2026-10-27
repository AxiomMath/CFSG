module

public import CFSG.Quasithin.Vol2.Ch1Inputs
public import CFSG.Quasithin.EmptyFaithful.SBd14Ctx

public section

namespace CFSG.Quasithin.SBd16

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Input15338CentV : Prop :=
  A312ForSQTK → ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    SBd14.RestHyp T Mc M V₁ V₂ Yp I L t → I = Subgroup.normalizer (V₁ : Set G) →
      ∀ v ∈ V₁, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤ I

end CFSG.Quasithin.SBd16

