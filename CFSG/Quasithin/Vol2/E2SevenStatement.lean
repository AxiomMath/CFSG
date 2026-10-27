module

public import CFSG.Quasithin.Vol2.E2StatementsAS

public section

namespace CFSG.Quasithin.ASInputs

open CFSG.Open CFSG.QuasithinUnique

@[expose] def AS_E_2_7C : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V : Subgroup G), E2.Hyp28 H T M V →
    kerIn M H = ⊥ → ¬ IsL33Exception H V → ∃ I : Subgroup G, IsInIHTVC H T M V I

@[expose] def AS_E_2_9_starSQTK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V : Subgroup G), E2.Hyp28 H T M V →
    SQTKGroup ↥(⊤ : Subgroup (E2.StarQuot M H))

end CFSG.Quasithin.ASInputs
