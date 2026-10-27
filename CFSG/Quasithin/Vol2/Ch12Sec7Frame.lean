module

public import CFSG.Quasithin.Background.C2Defs
public import CFSG.Quasithin.Background.F8Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

namespace S127

variable {G : Type} [Group G]

abbrev XOf (L : Subgroup G) : Subgroup G := oTwoUpper (oTwoZIn L)

@[expose] def IsFSub (L V W : Subgroup G) : Prop :=
  W ≤ V ∧ XOf L ≤ Subgroup.normalizer (W : Set G)

@[expose] def IsFPoint (L V W : Subgroup G) : Prop := IsFSub L V W ∧ Nat.card ↥W = 4

@[expose] def IsFLine (L V W : Subgroup G) : Prop := IsFSub L V W ∧ Nat.card ↥W = 16

@[expose] def V1 (T L V : Subgroup G) : Subgroup G :=
  V ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)

@[expose] def V2 (T L V : Subgroup G) : Subgroup G := ⁅V, T ⊓ L⁆

@[expose] def Pof (T L W : Subgroup G) : Subgroup G :=
  (L ⊔ pCoreOf 2 (L ⊔ T)) ⊓ Subgroup.normalizer (W : Set G)

abbrev P1 (T L V : Subgroup G) : Subgroup G := Pof T L (V1 T L V)

abbrev P2 (T L V : Subgroup G) : Subgroup G := Pof T L (V2 T L V)

abbrev R1 (T L V : Subgroup G) : Subgroup G := pCoreOf 2 (P1 T L V)

abbrev R2 (T L V : Subgroup G) : Subgroup G := pCoreOf 2 (P2 T L V)

@[expose] def L1 (T L V : Subgroup G) : Subgroup G :=
  oTwoUpper (L ⊓ Subgroup.centralizer (V1 T L V : Set G))

@[expose] def L2 (T L V : Subgroup G) : Subgroup G :=
  oTwoUpper (centralizerMod (V2 T L V) L V)

@[expose] def Vt (L : Subgroup G) (t : G) : Subgroup G := conjClosure (Subgroup.zpowers t) (XOf L)

@[expose] def Acts {V : Subgroup G} (y : MulAut ↥V) (W : Subgroup G) : Prop :=
  ∀ v : ↥V, (v : G) ∈ W → ((y v : ↥V) : G) ∈ W

end S127

end CFSG.Quasithin.H13
