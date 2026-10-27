module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatImg

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

@[expose] def Lemma14315Solvable : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Hyp1421 G T M → ¬ SixModels G →
    ¬ IsMulCommutative ↥(uOfL22 T M) → ∀ D : HatModel T M,
      Group.IsSolvable ↥(D.img (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)))

end CFSG.Quasithin
