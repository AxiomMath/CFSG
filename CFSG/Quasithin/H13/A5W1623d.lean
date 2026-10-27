module

public import CFSG.Quasithin.H13.A5S136h
public import CFSG.Quasithin.Background.A3Structure316

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def O3Prime1367 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∀ K : Subgroup G, K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)) → S.InYz K →
      S.Tv ≤ Subgroup.normalizer (K : Set G) →
      Nonempty (↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))) →
      K = oPrimeResidualOf 3 (Subgroup.centralizer ({S.v12} : Set G))

end CFSG.Quasithin.H13.A5
