module

public import CFSG.Quasithin.Background.RonanE114G2
public import CFSG.Quasithin.Background.RonanE114G2O2
public import CFSG.Quasithin.Background.RonanE114F4O2

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b

theorem quasithinIsSylowTwo_of_isSylowIn' {G : Type} [Group G] {T : Subgroup G}
    (h : IsSylowIn 2 T ⊤) : quasithinIsSylowTwo T :=
  ⟨h.2.1, by
    have h2 : ¬ 2 ∣ T.relIndex ⊤ := h.2.2
    rwa [Subgroup.relIndex_top_right] at h2⟩

section G2


theorem clause_one_G2_le
    (G : Type) [Group G] [Finite G] (T : Subgroup G) (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    ∀ n : ℕ, 1 ≤ n → IsG2 2 n ↥(CFSG.generalizedFitting G) →
      E1.nParam (⊤ : Subgroup G) ≤ (n : ℕ∞) :=
  fun _ _ hG2 => nParam_le_of_isG2 (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
    hT hFT hG2

theorem clause_one_G2
    (G : Type) [Group G] [Finite G] (T : Subgroup G) (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    ∀ n : ℕ, 1 ≤ n → IsG2 2 n ↥(CFSG.generalizedFitting G) →
      E1.nParam (⊤ : Subgroup G) = (n : ℕ∞) :=
  fun n hn hG2 => le_antisymm (clause_one_G2_le G T hSQ hFs hT hFT n hn hG2)
    (le_nParam_of_isG2 hFs (quasithinIsSylowTwo_of_isSylowIn' hT) hFT hG2)

end G2

section F4


theorem clause_one_2F4_le
    (G : Type) [Group G] [Finite G] (T : Subgroup G) (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    ∀ n : ℕ, 1 ≤ n → Is2F4 n ↥(CFSG.generalizedFitting G) →
      E1.nParam (⊤ : Subgroup G) ≤ (n : ℕ∞) :=
  fun _ _ h2F4 => nParam_le_of_is2F4
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2 hT hFT h2F4

theorem clause_one_2F4
    (G : Type) [Group G] [Finite G] (T : Subgroup G) (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    ∀ n : ℕ, 1 ≤ n → Is2F4 n ↥(CFSG.generalizedFitting G) →
      E1.nParam (⊤ : Subgroup G) = (n : ℕ∞) :=
  fun n hn h2F4 => le_antisymm (clause_one_2F4_le G T hSQ hFs hT hFT n hn h2F4)
    (le_nParam_of_is2F4 hFs (quasithinIsSylowTwo_of_isSylowIn' hT) hFT h2F4)

end F4

end CFSG.Quasithin.RonanE114
