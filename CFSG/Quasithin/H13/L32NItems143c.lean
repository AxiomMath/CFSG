module

public import CFSG.Quasithin.H13.L32NItems143

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def Lemma14333MEqL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp14310One G T L V →
    fsuV1 T V < centerOf (fsuU T V) → Subgroup.normalizer (L : Set G) = L

end CFSG.Quasithin.H13
