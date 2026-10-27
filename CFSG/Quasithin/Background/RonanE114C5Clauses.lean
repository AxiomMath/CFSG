module

public import CFSG.Quasithin.Background.RonanE114C5J1
public import CFSG.Quasithin.Background.RonanE114C5J2
public import CFSG.Quasithin.Background.RonanE114C5M22
public import CFSG.Quasithin.Background.RonanE114C5M23
public import CFSG.Quasithin.Background.RonanE114C5HS
public import CFSG.Quasithin.Background.RonanE114C5Ru

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b

theorem clause_five_J1
    (G : Type) [Group G] [Finite G] (T : Subgroup G) (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    IsSporadic .J1 ↥(CFSG.generalizedFitting G) → E1.nParam (⊤ : Subgroup G) ≤ 2 :=
  fun hL => by
    simpa using C5.J1.nParam_le_two_of_isJ1 hFs hL (quasithinIsSylowTwo_of_isSylowIn hT) hFT

theorem clause_five_J2
    (G : Type) [Group G] [Finite G] (T : Subgroup G) (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    IsSporadic .J2 ↥(CFSG.generalizedFitting G) → E1.nParam (⊤ : Subgroup G) ≤ 2 :=
  fun hL => by
    simpa using C5.J2.nParam_le_two_of_isJ2 hL (quasithinIsSylowTwo_of_isSylowIn hT) hFT

theorem clause_five_M22
    (G : Type) [Group G] [Finite G] (T : Subgroup G) (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    IsSporadic .M22 ↥(CFSG.generalizedFitting G) → E1.nParam (⊤ : Subgroup G) ≤ 2 :=
  fun hL => by
    simpa using C5.M22.nParam_le_two_of_isM22 hL (quasithinIsSylowTwo_of_isSylowIn hT) hFT

theorem clause_five_M23
    (G : Type) [Group G] [Finite G] (T : Subgroup G) (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    IsSporadic .M23 ↥(CFSG.generalizedFitting G) → E1.nParam (⊤ : Subgroup G) ≤ 2 :=
  fun hL => by
    simpa using C5.M23.nParam_le_two_of_isM23 hL (quasithinIsSylowTwo_of_isSylowIn hT) hFT

theorem clause_five_HS
    (G : Type) [Group G] [Finite G] (T : Subgroup G) (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    IsSporadic .HS ↥(CFSG.generalizedFitting G) → E1.nParam (⊤ : Subgroup G) ≤ 2 :=
  fun hL => by
    simpa using C5.HS.nParam_le_two_of_isHS hL (quasithinIsSylowTwo_of_isSylowIn hT) hFT

theorem clause_five_Ru
    (G : Type) [Group G] [Finite G] (T : Subgroup G) (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    IsSporadic .Ru ↥(CFSG.generalizedFitting G) → E1.nParam (⊤ : Subgroup G) ≤ 2 :=
  fun hL => by
    simpa using C5.Ru.nParam_le_two_of_isRu hL (quasithinIsSylowTwo_of_isSylowIn hT) hFT

theorem clause_five
    (G : Type) [Group G] [Finite G] (T : Subgroup G) (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤)
    (hJ4 : IsSporadic .J4 ↥(CFSG.generalizedFitting G) → E1.nParam (⊤ : Subgroup G) ≤ 2) :
    (IsSporadic .J1 ↥(CFSG.generalizedFitting G) ∨ IsSporadic .J2 ↥(CFSG.generalizedFitting G) ∨
        IsSporadic .J4 ↥(CFSG.generalizedFitting G) ∨
        IsSporadic .M22 ↥(CFSG.generalizedFitting G) ∨
        IsSporadic .M23 ↥(CFSG.generalizedFitting G) ∨
        IsSporadic .HS ↥(CFSG.generalizedFitting G) ∨
        IsSporadic .Ru ↥(CFSG.generalizedFitting G) → E1.nParam (⊤ : Subgroup G) ≤ 2) := by
  rintro (h | h | h | h | h | h | h)
  · exact clause_five_J1 G T hSQ hFs hT hFT h
  · exact clause_five_J2 G T hSQ hFs hT hFT h
  · exact hJ4 h
  · exact clause_five_M22 G T hSQ hFs hT hFT h
  · exact clause_five_M23 G T hSQ hFs hT hFT h
  · exact clause_five_HS G T hSQ hFs hT hFT h
  · exact clause_five_Ru G T hSQ hFs hT hFT h

end CFSG.Quasithin.RonanE114
