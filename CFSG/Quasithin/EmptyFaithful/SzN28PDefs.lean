module

public import CFSG.Quasithin.Background.G11Defs
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatImg

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.G11

@[expose] def Lemma14315Excl2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Hyp1421 G T M → ¬ SixModels G →
    ¬ IsMulCommutative ↥(uOfL22 T M) → ∀ D : HatModel T M,
      G112Concl2 (D.img (mcOf T)) → Group.IsSolvable ↥(D.img (mcOf T))

@[expose] def Lemma14315Excl4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Hyp1421 G T M → ¬ SixModels G →
    ¬ IsMulCommutative ↥(uOfL22 T M) → ∀ D : HatModel T M,
      G112Concl4 (D.img (mcOf T)) → Group.IsSolvable ↥(D.img (mcOf T))

@[expose] def Lemma14315Excl5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Hyp1421 G T M → ¬ SixModels G →
    ¬ IsMulCommutative ↥(uOfL22 T M) → ∀ D : HatModel T M,
      G112Concl5 D.B (D.img (mcOf T)) → Group.IsSolvable ↥(D.img (mcOf T))

@[expose] def Lemma14315Excl6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Hyp1421 G T M → ¬ SixModels G →
    ¬ IsMulCommutative ↥(uOfL22 T M) → ∀ D : HatModel T M,
      G112Concl6 (D.img (mcOf T)) → Group.IsSolvable ↥(D.img (mcOf T))

@[expose] def Lemma14315Excl11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Hyp1421 G T M → ¬ SixModels G →
    ¬ IsMulCommutative ↥(uOfL22 T M) → ∀ D : HatModel T M,
      G112Concl11 (D.img (mcOf T)) → Group.IsSolvable ↥(D.img (mcOf T))

end CFSG.Quasithin
