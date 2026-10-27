module

public import CFSG.Timmesfeld.CorollaryBQuot
public import CFSG.Timmesfeld.CorollaryBOutcome
public import CFSG.Timmesfeld.CorollaryBZStar
public import CFSG.Timmesfeld.CorollaryBDegen
public import Certificates.Certificate43
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate82
public import Certificates.Certificate83
public import Certificates.Certificate84
public import Certificates.Certificate85
public import Certificates.Certificate86
public import Certificates.Certificate87
public import Certificates.Certificate88
public import Certificates.Certificate89
public import Certificates.Certificate90
public import Certificates.Certificate91
public import Certificates.Certificate92
public import Certificates.Certificate93
public import Certificates.Certificate94
public import Certificates.Certificate95
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate1000
public import Certificates.Certificate1001
public import Certificates.Certificate1002
public import Certificates.Certificate1003
public import Certificates.Certificate1004
public import Certificates.Certificate1005
public import Certificates.Certificate1006
public import Certificates.Certificate1008
public import Certificates.Certificate1009
public import Certificates.Certificate1010
public import Certificates.Certificate1011
public import Certificates.Certificate1012
public import Certificates.Certificate1013
public import Certificates.Certificate1015
public import Certificates.Certificate1016
public import Certificates.Certificate1018
public import Certificates.Certificate1019
public import Certificates.Certificate3139
public import Certificates.Certificate7023
public import Certificates.Certificate8054
public import Certificates.Certificate8055
public import Certificates.Certificate8053
public import Certificates.Certificate8056
public import Certificates.Certificate1022
public import Certificates.Certificate7059
public import Certificates.Certificate15950
public import Certificates.Certificate15952
public import Certificates.Certificate15953
public import Certificates.Certificate15951
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.Uniqueness.Bender.OddCentralizer
public import CFSG.GH74.Uniqueness.Bender.Unitary
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitary
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Monster.Code.Weights
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.Module
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Th.Max3.Involutions
public import Certificates.Certificate10089Base
public import Certificates.Certificate10091Base

public section

namespace CFSG.Timmesfeld.CorB

open Subgroup

variable {X : Type} [Group X] [Finite X] {t : X}

theorem main (h : Setup t) :
    (∃ K : Subgroup X, K ≤ normalClosure ({t} : Set X) ∧
        (K.subgroupOf (normalClosure ({t} : Set X))).Normal ∧ Odd (Nat.card K) ∧
        normalClosure ({t} : Set X) = K ⊔ zpowers t) ∨
      (∀ x ∈ normalClosure ({t} : Set X), ∀ y ∈ normalClosure ({t} : Set X),
        x * y = y * x ∧ x * x = 1) ∨
      ((∀ d ∈ cls t, ∀ e ∈ cls t, orderOf (d * e) ≠ 4) ∧
        CFSG.BenderSuzuki.IsBenderGroup
          (↥(normalClosure ({t} : Set X)) ⧸ center ↥(normalClosure ({t} : Set X)))) ∨
      (Hyp (↥(normalClosure ({t} : Set X)) ⧸ center ↥(normalClosure ({t} : Set X)))
          (QuotientGroup.mk' (center ↥(normalClosure ({t} : Set X))) '' clsIn t) ∧
        OutcomeTwo (↥(normalClosure ({t} : Set X)) ⧸ center ↥(normalClosure ({t} : Set X)))
          (QuotientGroup.mk' (center ↥(normalClosure ({t} : Set X))) '' clsIn t)) := by
  by_cases hpair : ∃ τ ∈ conjCent t, τ ≠ t
  · by_cases hdeg : ∀ d ∈ cls t, ∀ e ∈ cls t, orderOf (d * e) ≠ 4
    · rcases h.degenerate hpair hdeg with h2 | hB
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inl ⟨hdeg, hB⟩))
    · push Not at hdeg
      have hH := h.hyp_quotient hpair hdeg
      exact Or.inr (Or.inr (Or.inr ⟨hH, outcomeTwo_of_noOddCent hH (h.noOddCent_quotient hdeg)⟩))
  · push Not at hpair
    exact Or.inl (zStar_case h.orderOf_eq fun τ hτt hτ => hpair τ ⟨hτt, hτ⟩)

end CFSG.Timmesfeld.CorB
