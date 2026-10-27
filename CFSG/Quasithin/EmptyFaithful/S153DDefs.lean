module

public import CFSG.Quasithin.EmptyFaithful.S153Plus

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G]

abbrev YL153 (Yp L : Subgroup G) : Subgroup G := oTwoUpper (Yp ⊓ L)

abbrev YC153 (Yp L : Subgroup G) : Subgroup G :=
  oTwoUpper (centralizerSection Yp L (pCoreOf 2 L))

abbrev WL153 (T M L : Subgroup G) : Subgroup G := conjClosure (VZ T M) L

structure Facts15311 [Finite G] (T M V₁ Yp I : Subgroup G) : Prop where
  sylow : IsSylowTwoOf (Sgp153 T V₁) I
  cent_le : I ⊓ Subgroup.centralizer (UI153 T I : Set G) ≤ M ⊓ I
  norm_eq : I ⊓ Subgroup.normalizer (Yp : Set G) = M ⊓ I
  struct_Yp : IsElemAbelianOfRank 3 2 (OTwoQuot Yp) ∨ IsPOnePlusTwo 3 (OTwoQuot Yp)
  R_eq : R153 T V₁ Yp = T ⊓ Subgroup.centralizer (VZ T M : Set G)
  radical : IsTwoRadicalIn I (R153 T V₁ Yp)
  sylow_R : IsSylowTwoOf (R153 T V₁ Yp) (conjClosure (R153 T V₁ Yp) (M ⊓ I))
  cgs : CGS (R153 T V₁ Yp) ≤ M
  theta : Yp = thetaOf (M ⊓ I)
  star_norm : Subgroup.normalizer (autOn Yp (UI153 T I) : Set (MulAut ↥(UI153 T I))) ⊓
    autOn I (UI153 T I) = autOn (M ⊓ I) (UI153 T I)
  star_lt : autOn (M ⊓ I) (UI153 T I) < autOn I (UI153 T I)
  star_ne : autOn Yp (UI153 T I) ≠ ⊥
  J_not_le : ¬ autOn (thompsonJ I) (UI153 T I) ≤ autOn (M ⊓ I) (UI153 T I)

structure Ctx15313 [Finite G] (T Mc M V₁ V₂ Yp I : Subgroup G) (t : G) : Prop where
  hyp : Hyp15310 G T Mc M V₁ V₂ Yp t
  inH : IsHPlus Yp (Sgp153 T V₁) M I
  rank : CFSG.Open.pRank 3 Yp = 2
  charTwo : CharTwo I

end CFSG.Quasithin
