module

public import CFSG.Quasithin.Background.S1549CStar
public import CFSG.Quasithin.Background.S1549CFDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

namespace S1549C

section Vocabulary

variable {G : Type} [Group G]

abbrev UTil (T M V₁ H : Subgroup G) : Type :=
  ↥(tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H))

noncomputable abbrev StarOf (T M V₁ H X : Subgroup G) : Subgroup (MulAut (UTil T M V₁ H)) :=
  autOn (tildeOf (quasithinOmegaOneCenter T) X) (tildeOf (quasithinOmegaOneCenter T) (UH T M V₁ H))

end Vocabulary

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

structure InspBase (cx : Ctx49 G T Mc M V₁ V₂ t) (H : Subgroup G) : Prop where
  adm : Adm T Mc M H
  min : ∀ H' : Subgroup G, Adm T Mc M H' → H' ≤ H → H' = H
  claimB : Y0 T Mc M = thetaOf (M ⊓ H)
  claimC : ClaimC T M V₁ H
  claimD : IsElemAbelian 2 (VH T M H)
  hF98 : HypF98 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H

structure OffData {cx : Ctx49 G T Mc M V₁ V₂ t} {H : Subgroup G} (hb : InspBase cx H)
    (W : Subgroup G) (B : Subgroup (MulAut (UTil T M V₁ H))) : Prop where
  W_le : W ≤ pCoreOf 2 (Y0 T Mc M ⊔ T)
  B_le : B ≤ StarOf T M V₁ H W
  off : @IsFFStarOffender (UTil T M V₁ H) (modInst hb.hF98.toHypF91) (StarOf T M V₁ H H) B

@[expose] noncomputable def Jgrp {cx : Ctx49 G T Mc M V₁ V₂ t} {H : Subgroup G} (hb : InspBase cx H)
    (B : Subgroup (MulAut (UTil T M V₁ H))) : Subgroup G :=
  preStar hb.hF98.toHypF91 (conjClosure B (StarOf T M V₁ H H))

end S1549C

end CFSG.Quasithin
