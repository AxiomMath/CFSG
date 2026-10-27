module

public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.B4ModelsLie
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

@[expose] def AsI16CoverA8 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) → ∀ L : Subgroup (MulAut V),
    commV L ∈ IrrPlus L ⊤ → SLExteriorTwo L (commV L) (fixV L ⊓ commV L) 4 →
      Nat.card ↥(fixV L ⊓ commV L) ≤ 2

end CFSG.Quasithin
