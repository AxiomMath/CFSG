module

public import CFSG.Quasithin.EmptyFaithful.S153DInputs
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

@[expose] def Concl15312Two {G : Type} [Group G] (Yp L : Subgroup G) : Prop :=
  Yp = YL153 Yp L ⊔ YC153 Yp L ∧ padicValNat 3 (Nat.card ↥(YL153 Yp L)) = 1 ∧
    padicValNat 3 (Nat.card ↥(YC153 Yp L)) = 1 ∧ IsElemAbelianOfRank 3 2 (OTwoQuot Yp)

@[expose] def Concl15314Two {G : Type} [Group G] (T Mc M : Subgroup G) : Prop :=
  IsPOnePlusTwo 3 (OTwoQuot (Y153 Mc M)) ∧
    (pCoreOf 2 (Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G))).relIndex
      (Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G)) = 3

@[expose] def Input15312TwoL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → IsLnTwoQuot L 3 → Concl15312Two Yp L

@[expose] def Input15314Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I : Subgroup G) (t : G),
    Ctx15313 T Mc M V₁ V₂ Yp I t →
      (IsUniqueM (Y153 Mc M ⊔ Sgp153 T V₁) M ∧
        Yp = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G))) → Concl15314Two T Mc M

end CFSG.Quasithin
