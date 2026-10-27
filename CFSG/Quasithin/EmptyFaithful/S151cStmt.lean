module

public import CFSG.Quasithin.EmptyFaithful.S151Statements

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def CentralOnComplement1512 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M →
    ⁅VZ T M ⊓ Subgroup.centralizer
        (preOn M (VZ T M) (fittingIn (JhatOn M (VZ T M))) : Set G), mJ154 T M⁆ = ⊥

@[expose] def Description1512CE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M →
    V154 T Mc M = conjClosure (quasithinOmegaOneCenter T ⊓ V154 T Mc M) (m0Of T Mc M)

@[expose] def Nilpotency1512CE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M → IsTwoNilpotentOn M (V154 T Mc M)

end CFSG.Quasithin
