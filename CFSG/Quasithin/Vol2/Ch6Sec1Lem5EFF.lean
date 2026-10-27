module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5Cut

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Res615EFF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H : Subgroup G) (n : ℕ),
    Cx615C G T M L V H n →
      ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G) →
      ∃ z ∈ quasithinOmegaOneCenter T ⊓
          ⁅conjClosure (quasithinOmegaOneCenter T) (borelL T L ⊔ H), borelL T L ⊔ H⁆,
        z ≠ 1 ∧ (∃ d ∈ borelL T L, Odd (orderOf d) ∧ d ≠ 1 ∧ d * z * d⁻¹ = z) ∧
        ¬ (borelL T L ⊔ H) ⊓ Subgroup.centralizer ({z} : Set G) ≤
          Subgroup.normalizer ((borelL T L : Subgroup G) : Set G)

end CFSG.Quasithin.H13
