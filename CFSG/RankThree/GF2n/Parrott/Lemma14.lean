module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Recognition.U33Defs
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Parrott.LocalData

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

noncomputable abbrev utH : ↥(H z) := uH D * tH D

abbrev HModJ (z : G) [hN : ((J z).subgroupOf (H z)).Normal] : Type :=
  ↥(H z) ⧸ (J z).subgroupOf (H z)

noncomputable def utq : HModJ (z := z) :=
  QuotientGroup.mk' ((J z).subgroupOf (H z)) (utH D)

noncomputable def CHutQuot : Subgroup (HModJ (z := z)) :=
  Subgroup.centralizer ({utq (z := z) (D := D)} : Set (HModJ (z := z)))

def ConjMeetJBot (K : Subgroup (J z)) (y : G) : Prop :=
  (K.map (J z).subtype).map (MulAut.conj y).toMonoidHom ⊓ J z = ⊥

def NoZ4Q8InCHutQuot (D : QuotientData (z := z) hN) : Prop :=
  ∀ L : Subgroup (HModJ (z := z)), L ≤ CHutQuot (z := z) (D := D) →
    ¬ Nonempty (↥L ≃* CFSG.Quasithin.Z4StarQ8Model)

end CFSG.RankThree.GF2n.Parrott
