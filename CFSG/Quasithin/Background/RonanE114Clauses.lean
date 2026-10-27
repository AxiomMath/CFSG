module

public import CFSG.Quasithin.Background.RonanE114Lie
public import CFSG.Quasithin.Background.RonanE114Tits
public import CFSG.Quasithin.Background.RonanE114M11
public import CFSG.Quasithin.Background.RonanE114M12
public import CFSG.Quasithin.Background.RonanE114M24
public import CFSG.Quasithin.Background.RonanE114L2Main
public import CFSG.Quasithin.Background.RonanE114U33
public import CFSG.Quasithin.Background.RonanE114L42

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b

theorem quasithinIsSylowTwo_of_isSylowIn {G : Type} [Group G] {T : Subgroup G}
    (h : IsSylowIn 2 T ⊤) : quasithinIsSylowTwo T :=
  ⟨h.2.1, by
    have h2 : ¬ 2 ∣ T.relIndex ⊤ := h.2.2
    rwa [Subgroup.relIndex_top_right] at h2⟩

theorem clause_one_typeLie
    (G : Type) [Group G] [Finite G] (T : Subgroup G) (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    ∀ n : ℕ, 1 ≤ n →
      (IsPSL 2 2 n ↥(CFSG.generalizedFitting G) ∨ IsSz n ↥(CFSG.generalizedFitting G) ∨
        IsPSU 3 2 n ↥(CFSG.generalizedFitting G) ∨ IsPSL 3 2 n ↥(CFSG.generalizedFitting G) ∨
        IsPSp4 2 n ↥(CFSG.generalizedFitting G) ∨
        (n = 1 ∧ IsAlt 6 ↥(CFSG.generalizedFitting G))) →
        E1.nParam (⊤ : Subgroup G) = (n : ℕ∞) :=
  fun _ hn hL => nParam_eq_of_typeLie hSQ hFs (quasithinIsSylowTwo_of_isSylowIn hT) hFT hn hL

theorem clause_one_tits
    (G : Type) [Group G] [Finite G] (T : Subgroup G) (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    IsTits ↥(CFSG.generalizedFitting G) → E1.nParam (⊤ : Subgroup G) = 1 :=
  fun hL => nParam_eq_one_of_isTits hL (quasithinIsSylowTwo_of_isSylowIn hT) hFT

theorem clause_one_u33
    (G : Type) [Group G] [Finite G] (T : Subgroup G) (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    IsPSU 3 3 1 ↥(CFSG.generalizedFitting G) → E1.nParam (⊤ : Subgroup G) = 1 :=
  fun hL => nParam_eq_one_of_isPSU33 hL (quasithinIsSylowTwo_of_isSylowIn hT) hFT

theorem clause_one_l42
    (G : Type) [Group G] [Finite G] (T : Subgroup G) (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    IsPSL 4 2 1 ↥(CFSG.generalizedFitting G) → E1.nParam (⊤ : Subgroup G) = 1 :=
  fun hL => nParam_eq_one_of_isPSL42 hL (quasithinIsSylowTwo_of_isSylowIn hT) hFT

theorem clause_three
    (G : Type) [Group G] [Finite G] (T : Subgroup G) (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    IsAlt 7 ↥(CFSG.generalizedFitting G) → E1.nParam (⊤ : Subgroup G) = 1 :=
  fun hL => nParam_eq_one_of_isAlt7 hL

theorem clause_four_M11
    (G : Type) [Group G] [Finite G] (T : Subgroup G) (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    IsSporadic .M11 ↥(CFSG.generalizedFitting G) → E1.nParam (⊤ : Subgroup G) = 1 :=
  fun hL => nParam_eq_one_of_isM11 hL (quasithinIsSylowTwo_of_isSylowIn hT) hFT

theorem clause_four_M12
    (G : Type) [Group G] [Finite G] (T : Subgroup G) (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    IsSporadic .M12 ↥(CFSG.generalizedFitting G) → E1.nParam (⊤ : Subgroup G) = 1 :=
  fun hL => nParam_eq_one_of_isM12 hL (quasithinIsSylowTwo_of_isSylowIn hT) hFT

theorem clause_four_M24
    (G : Type) [Group G] [Finite G] (T : Subgroup G) (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    IsSporadic .M24 ↥(CFSG.generalizedFitting G) → E1.nParam (⊤ : Subgroup G) = 1 :=
  fun hL => nParam_eq_one_of_isM24 hL (quasithinIsSylowTwo_of_isSylowIn hT) hFT

theorem clause_six
    (G : Type) [Group G] [Finite G] (T : Subgroup G) (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    ∀ p e : ℕ, p.Prime → p ≠ 2 → 5 < p ^ e → IsPSL 2 p e ↥(CFSG.generalizedFitting G) →
      E1.nParam (⊤ : Subgroup G) = 1 :=
  fun _ _ hp hp2 h5 hF =>
    nParam_eq_one_of_isPSL2 hSQ hFs (quasithinIsSylowTwo_of_isSylowIn hT) hFT hp hp2 h5 hF

end CFSG.Quasithin.RonanE114
