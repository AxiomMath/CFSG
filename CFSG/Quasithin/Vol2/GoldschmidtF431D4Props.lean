module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Stab
public import CFSG.Quasithin.Background.F1Amalgam

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.Quasithin

universe u

@[expose] def d4IsoV1 {X Y : Type u} [Group X] [Group Y] {A B : Subgroup X} {A' B' : Subgroup Y}
    (e : (RankTwoAmalgam.ofSubgroups A B).Iso (RankTwoAmalgam.ofSubgroups A' B')) :
    ↥A ≃* ↥A' := e.φ1

@[expose] def d4IsoV2 {X Y : Type u} [Group X] [Group Y] {A B : Subgroup X} {A' B' : Subgroup Y}
    (e : (RankTwoAmalgam.ofSubgroups A B).Iso (RankTwoAmalgam.ofSubgroups A' B')) :
    ↥B ≃* ↥B' := e.φ2


@[expose] def D4LocalCent (zH tH : ↥d4H) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H₁ H₂ : Subgroup G)
    (e : (RankTwoAmalgam.ofSubgroups d4H d4N).Iso (RankTwoAmalgam.ofSubgroups H₁ H₂)),
    Subgroup.centralizer ({((d4IsoV1 e zH : ↥H₁) : G)} : Set G) ≤ H₁ →
      Subgroup.centralizer ({((d4IsoV1 e tH : ↥H₁) : G)} : Set G) ≤ H₂

@[expose] def D4NonFusion (zH tH : ↥d4H) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H₁ H₂ : Subgroup G)
    (e : (RankTwoAmalgam.ofSubgroups d4H d4N).Iso (RankTwoAmalgam.ofSubgroups H₁ H₂)),
    Subgroup.centralizer ({((d4IsoV1 e zH : ↥H₁) : G)} : Set G) ≤ H₁ →
      ¬ IsConj ((d4IsoV1 e zH : ↥H₁) : G) ((d4IsoV1 e tH : ↥H₁) : G)

end CFSG.Quasithin.D4Hex
