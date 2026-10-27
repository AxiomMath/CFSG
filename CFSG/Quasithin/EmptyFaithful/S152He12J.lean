module

public import CFSG.Quasithin.EmptyFaithful.S152He12F
public import CFSG.Quasithin.EmptyFaithful.S152WAtlas
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ4CoverCert
public import CFSG.Quasithin.EmptyFaithful.S152VJ4b
public import CFSG.Quasithin.EmptyFaithful.S152VKcIii

public section

namespace CFSG.Quasithin

theorem tail15215CoreW_of_certificates
    (hA3 : ∀ (G : Type) [Group G] [Finite G], A3Orbits G) : He12.Tail15215CoreW :=
  He12.tail15215CoreW_of_four (tail15215L2p_of hA3)
    (tail15215Rank_of hA3 CFSG.ComponentClassification.RankTwoSporadic.J4.j4NoDoubleCover_checked
      sporadicInvolution3Rank_of_certificates)
    tail15215J4_of tail15215Kc

end CFSG.Quasithin
