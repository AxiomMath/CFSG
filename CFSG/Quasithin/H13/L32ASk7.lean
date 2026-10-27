module

public import CFSG.Quasithin.H13.L32ASetting

public section

namespace CFSG.Quasithin.H13

@[expose] def Lemma14_7_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    IsPGroup 3 ↥(CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H))

end CFSG.Quasithin.H13
