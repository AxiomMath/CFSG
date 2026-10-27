module

public import CFSG.Quasithin.Vol2.Ch12Sec6Final

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin S126

@[expose] def NoFF12632 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ H K : Subgroup G, IsHK T L F.V1 H K → Case1 T L H K → HypF918 T V L F.V1 F.V5 H K →
        ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
          ∀ ρ : ↥(K ⊔ T) →* MulAut W,
            (∀ x : ↥(K ⊔ T), (x : G) ∈ pCoreOf 2 H → ρ x = 1) →
            (∀ x : ↥(K ⊔ T), (x : G) ∈ K → ρ x = 1 →
              ∀ k ∈ K, (x : G) * k * (x : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 H) →
            ¬ IsFFModule ρ.range

end CFSG.Quasithin.H13
