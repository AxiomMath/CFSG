module

public import CFSG.Quasithin.Vol2.Ch4Sec2Lem4212C

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13

@[expose] def Conf4212NoJ4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G),
    Hyp4_2_3 G T M L Mm I → InM I H → Conf4212 G T M L I H K →
      ¬ C48Case6 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K

end CFSG.Quasithin.H13.Ch4
