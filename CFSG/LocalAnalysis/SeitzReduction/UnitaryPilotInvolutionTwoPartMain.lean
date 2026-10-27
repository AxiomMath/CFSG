module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPart
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapUniqueMain

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

section SeitzFull

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  (h : UnitaryFieldData 2 f K) {m : ℕ}

theorem false_of_seitzSetting_unitary_of_cat (hset : SeitzSetting G L)
    (hcat : SUmCatalogueClausesAt (m + 1 - 2)) (e : L ≃* unitaryPSU h (m + 1)) (hm : 5 ≤ m)
    (hnf : (m + 1, f) ≠ (6, 1)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) : False :=
  false_of_seitzSetting_unitary_of_innerTwoPart h (unitaryInnerInvolutionTwoPart_holds h (m + 1))
    hset hcat e hm hnf ht hKt

end SeitzFull

end CFSG.SeitzReduction.UnitaryPilot
