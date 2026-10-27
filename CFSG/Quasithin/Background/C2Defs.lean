
module

public import CFSG.Quasithin.Background.C1Basic
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Series

variable {G : Type*} [Group G]

@[expose] def preimageModTwoCore (H : Subgroup G) (P : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
    Subgroup G :=
  (P.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype

@[expose] def oTwoFIn (H : Subgroup G) : Subgroup G :=
  preimageModTwoCore H (CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H))

@[expose] def oTwoFstarIn (H : Subgroup G) : Subgroup G :=
  preimageModTwoCore H (CFSG.generalizedFitting (↥H ⧸ CFSG.pCore 2 ↥H))

@[expose] def oTwoEIn (H : Subgroup G) : Subgroup G :=
  preimageModTwoCore H (CFSG.layer (↥H ⧸ CFSG.pCore 2 ↥H))

@[expose] def oTwoZIn (L : Subgroup G) : Subgroup G :=
  preimageModTwoCore L (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))

@[expose] def oTwoThreeIn (H : Subgroup G) : Subgroup G :=
  preimageModTwoCore H (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H))

@[expose] def conjByElt (t : G) (K : Subgroup G) : Subgroup G :=
  K.map (MulAut.conj t).toMonoidHom

theorem mem_conjByElt {t x : G} {K : Subgroup G} : x ∈ conjByElt t K ↔ t⁻¹ * x * t ∈ K := by
  unfold conjByElt
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

@[expose] def IsBorelOfBlock (L B : Subgroup G) : Prop :=
  if Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3 then B ≤ pCoreOf 2 L
  else ∃ S : Subgroup G, IsSylowTwoOf S L ∧
    B ⊔ pCoreOf 2 L = L ⊓ Subgroup.normalizer (S : Set G)

end Series

section Hypotheses

variable {G : Type} [Group G] [Finite G]

@[expose] def IsSQTKIn (H : Subgroup G) : Prop := SQTKGroup ↥H

structure HypC23 (H R M : Subgroup G) : Prop where
  sqtk : IsSQTKIn H
  radical : IsTwoRadicalIn H R
  le : M ≤ H
  cgs : cgsIn H R ≤ M
  sylow : IsSylowTwoOf R (conjClosure R M)

structure HypC28 (H R M L V : Subgroup G) : Prop where
  sqtk : IsSQTKIn H
  pgroup : IsPGroup 2 R
  le_M : R ≤ M
  le_H : M ≤ H
  charTwo : CharTwo M
  pCore_ne : pCoreOf 2 H ≠ ⊥
  comp : L ∈ cComp M
  sylow : IsSylowTwoOf R
    (centralizerSection M (conjClosure L M) (pCoreOf 2 (conjClosure L M)))
  cgs : cgsIn H R ≤ M
  V_le : V ≤ conjClosure L M
  V_ne : V ≠ ⊥
  V_elem : IsElemAbelian 2 V
  V_comm : ⁅V, conjClosure L M⁆ = V
  V_center : V ≤ centerOf (pCoreOf 2 (conjClosure L M ⊔ R))
  V_norm : H ⊓ Subgroup.normalizer (V : Set G) ≤ M

end Hypotheses

end CFSG.Quasithin
