module

public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.ConjShared

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem ElevenOneHyp.conj {hC : HypothesisC D} (h : ElevenOneHyp hC) (g : G) :
    ElevenOneHyp (hC.conj g) where
  rad := h.rad
  center := by
    rw [← conjRadical_map hC g, h.center]
    exact Subgroup.map_center_eq (conjEquiv hC g)
  facts :=
    O4PlusFacts.of_mulEquiv
      (QuotientGroup.congr (CFSG.solvableRadical (Halpha D hC.alpha))
        (CFSG.solvableRadical (Halpha D (hC.conj g).alpha)) (conjEquiv hC g)
        (conjRadical_map hC g)) (imageClass_conj hC g) h.facts

end CFSG.OddTranspositions.PartThree
