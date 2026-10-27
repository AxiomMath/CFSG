module

public import CFSG.Quasithin.Vol2.Ch12Sec7I77a

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Quasithin S127 S127.I77

@[expose] def MEqNormV1277 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (t : G), Set77 G T L V t →
    Subgroup.normalizer (L : Set G) = Subgroup.normalizer (V : Set G)

end CFSG.Quasithin.H13.I1277
