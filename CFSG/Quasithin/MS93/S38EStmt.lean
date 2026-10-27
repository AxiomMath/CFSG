module

public import CFSG.Quasithin.MS93.S38EFFHyp
public import CFSG.Quasithin.MS93.S38PU
public import CFSG.Quasithin.MS93.SkItems

public section

namespace CFSG.Quasithin.MS93.S38E

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

@[expose] def SL3SecBound : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G), PUHyp M T L →
    T ⊓ Subgroup.centralizer (Z0q M T : Set G) = pCoreOf 2 M → IsDoubleSL3U M T L →
    ∀ F : Subgroup G, IsXOff M T F →
    ∀ (S : Type) [CommGroup S] [Finite S] (ρ : ↥M →* MulAut S), IsIrrRep L ρ →
    ∀ (Fq : Type) [Field Fq] [Finite Fq],
      ((FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 Fq)).Realizes (IsIrrRep.imL L ρ) ⊤ ⊥ ∨
        DirectSumOfCopies (IsIrrRep.imL L ρ) ⊤ ⊥
          (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 Fq)) 2) →
      Nat.card Fq ^ 3 ≤ (fixV ((F.subgroupOf M).map ρ)).index *
        Nat.card (commV ((F.subgroupOf M).map ρ))

end CFSG.Quasithin.MS93.S38E
