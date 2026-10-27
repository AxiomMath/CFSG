module

public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatImg

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace SzPS8

@[expose] def Excl2NoNormalA5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Hyp1421 G T M → ¬ SixModels G →
    ¬ IsMulCommutative ↥(uOfL22 T M) → ∀ D : HatModel T M, Module.finrank (ZMod 2) D.V = 4 →
      ¬ ∃ N : Subgroup ↥(D.img (mcOf T)), N.Normal ∧
        Nonempty (↥N ≃* ↥(alternatingGroup (Fin 5)))

@[expose] def Excl2NoNormalA6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Hyp1421 G T M → ¬ SixModels G →
    ¬ IsMulCommutative ↥(uOfL22 T M) → ∀ D : HatModel T M, Module.finrank (ZMod 2) D.V = 4 →
      ¬ ∃ N : Subgroup ↥(D.img (mcOf T)), N.Normal ∧
        Nonempty (↥N ≃* ↥(alternatingGroup (Fin 6)))

end SzPS8

end CFSG.Quasithin
