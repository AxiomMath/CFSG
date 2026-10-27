module

public import CFSG.OddTranspositions.PartThree.Eleven.PlusFacts
public import CFSG.OddTranspositions.PartThree.Eleven.Injective
public import CFSG.OddTranspositions.PartThree.Eleven.Primitive

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

structure ElevenOneHyp (hC : HypothesisC D) : Prop where
  rad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥
  center : CFSG.solvableRadical (Halpha D hC.alpha) = Subgroup.center (Halpha D hC.alpha)
  facts : O4PlusFacts (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))
    (imageClass hC)

@[expose] def liftH (hC : HypothesisC D)
    (A : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) :
    Subgroup G :=
  (A.comap (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))).map
    (Halpha D hC.alpha).subtype

namespace ElevenOneHyp

variable {hC : HypothesisC D}

theorem injOn (h : ElevenOneHyp hC) :
    Set.InjOn (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) (DstarH hC) :=
  injOn_mk_DstarH hC h.center h.facts.noncomm

theorem alpha_eq (h : ElevenOneHyp hC) : hC.alpha = {hC.d} :=
  alpha_eq_singleton hC h.injOn h.facts.primitive

end ElevenOneHyp

end CFSG.OddTranspositions.PartThree
