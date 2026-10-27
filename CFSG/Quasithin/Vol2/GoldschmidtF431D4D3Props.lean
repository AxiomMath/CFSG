module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Props
public import CFSG.Quasithin.EmptyFaithful.S1421Inputs

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.Quasithin


@[expose] def D3LocalCent (zH tH : ↥(autStab d4H)) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H₁ H₂ : Subgroup G)
    (e : (RankTwoAmalgam.ofSubgroups (autStab d4H) (autStab d4N)).Iso
      (RankTwoAmalgam.ofSubgroups H₁ H₂)),
    Subgroup.centralizer ({((d4IsoV1 e zH : ↥H₁) : G)} : Set G) ≤ H₁ →
      Subgroup.centralizer ({((d4IsoV1 e tH : ↥H₁) : G)} : Set G) ≤ H₂

@[expose] def D3NonFusion (zH tH : ↥(autStab d4H)) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H₁ H₂ : Subgroup G)
    (e : (RankTwoAmalgam.ofSubgroups (autStab d4H) (autStab d4N)).Iso
      (RankTwoAmalgam.ofSubgroups H₁ H₂)),
    Subgroup.centralizer ({((d4IsoV1 e zH : ↥H₁) : G)} : Set G) ≤ H₁ →
      ¬ IsConj ((d4IsoV1 e zH : ↥H₁) : G) ((d4IsoV1 e tH : ↥H₁) : G)

end CFSG.Quasithin.D4Hex
