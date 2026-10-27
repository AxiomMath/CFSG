module

public import CFSG.OddTranspositions.PartThree.Eleven.Statements
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Hyp
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Pair
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Quandle
public import CFSG.OddTranspositions.PartThree.EightFive.KBarSetup
public import Certificates.Certificate2326
public import CFSG.OddTranspositions.PartThree.Eleven.MinusFacts
import CFSG.OddTranspositions.PartThree.Nine.Setup
import CFSG.OddTranspositions.PartThree.Eleven.GroupLemmas
public import Certificates.Kernel.SporSch.Th.Key2311
public import Certificates.Kernel.SporSch.Th.Orb2315
public import Certificates.Kernel.SporSch.Th.Plane2320

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

section Hyp

variable {G : Type} [Group G] [Finite G] {D : Set G}

structure ElevenTwoHyp (hC : HypothesisC D) : Prop where
  rad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥
  center : CFSG.solvableRadical (Halpha D hC.alpha) = Subgroup.center (Halpha D hC.alpha)
  facts : O4MinusFacts (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))
    (imageClass hC)

namespace ElevenTwoHyp

variable {hC : HypothesisC D}

theorem injOn (h : ElevenTwoHyp hC) :
    Set.InjOn (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) (DstarH hC) :=
  injOn_mk_DstarH hC h.center h.facts.noncomm

theorem alpha_eq (h : ElevenTwoHyp hC) : hC.alpha = {hC.d} :=
  alpha_eq_singleton hC h.injOn h.facts.primitive

theorem DalphaStar_eq (h : ElevenTwoHyp hC) : DalphaStar D hC.alpha = commSet D hC.d :=
  Nine.DalphaStar_eq_commSet hC h.alpha_eq

theorem radical_le_commutator (h : ElevenTwoHyp hC) :
    CFSG.solvableRadical (Halpha D hC.alpha) ≤ commutator (Halpha D hC.alpha) := by
  have hindex_le : (commutator (Halpha D hC.alpha)).index ≤ 2 :=
    (⟨DstarH_isClass hC, DstarH_isOddTransp hC, DstarH_closure_eq_top hC⟩ :
      Setup (Halpha D hC.alpha) (DstarH hC)).index_commutator_le_two
  have hQ : (commutator (Halpha D hC.alpha ⧸
      CFSG.solvableRadical (Halpha D hC.alpha))).index = 2 := h.facts.index_two
  exact le_commutator_of_index_commutator_quotient
    (CFSG.solvableRadical (Halpha D hC.alpha)) hindex_le hQ

end ElevenTwoHyp

end Hyp

end CFSG.OddTranspositions.PartThree
