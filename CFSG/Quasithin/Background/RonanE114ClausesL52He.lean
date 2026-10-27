module

public import CFSG.Quasithin.Background.RonanE114Clauses
public import CFSG.Quasithin.Background.RonanE114L52
public import CFSG.Quasithin.Background.RonanE114HeMain

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b

theorem clause_one_l52
    (G : Type) [Group G] [Finite G] (T : Subgroup G) (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    IsPSL 5 2 1 ↥(CFSG.generalizedFitting G) → E1.nParam (⊤ : Subgroup G) = 1 :=
  fun hL => nParam_eq_one_of_isPSL52 hL (quasithinIsSylowTwo_of_isSylowIn hT) hFT

theorem clause_four_He
    (G : Type) [Group G] [Finite G] (T : Subgroup G) (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    IsSporadic .He ↥(CFSG.generalizedFitting G) → E1.nParam (⊤ : Subgroup G) = 1 :=
  fun hL => nParam_eq_one_of_isHe hL (quasithinIsSylowTwo_of_isSylowIn hT) hFT

end CFSG.Quasithin.RonanE114
