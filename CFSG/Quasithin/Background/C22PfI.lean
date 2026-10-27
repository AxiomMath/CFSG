module

public import CFSG.Quasithin.Background.C22PfF
public import CFSG.Quasithin.Background.C22PfH
public import CFSG.LieType.BorelTits.AllModels

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Blueprint

namespace C22Pf

theorem isRadicalParabolic_c224_holds
    (X : Type) [Group X] [Finite X]
    (hX : EvenLieType X ∨ IsAlt 6 X ∨ IsPSU 3 3 1 X) :
    SmithC27.IsRadicalParabolic (⊤ : Subgroup X) :=
  isRadicalParabolic_c224 (fun _ _ _ _ _ h ht => holds_of_lieModel h ht)
    (fun _ _ _ _ h => holdsTits_of_lieModel_tits h) titsSylowSelfNormalizing_holds
    radicalParabolicU33_holds hX

variable {G : Type} [Group G] [Finite G]

theorem asc22Statement_holds
    (hA37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y) :
    ASC22Statement G :=
  asc22Statement_of hA37 isRadicalParabolic_c224_holds

end C22Pf

end CFSG.Quasithin
