module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NOneD
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NTwoI
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsF
public import CFSG.LieType.SuzukiSubgroups.Input
public import CFSG.LocalAnalysis.WeakClosure81.TwoConjugateSzProof

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open Subgroup

variable {G : Type} [Group G] [Finite G]

section Certified


theorem Cfg1620.false_of_two_lt_mBar {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}
    (hTim : TimmesfeldTIRootInput) (hCore : OddTranspositionCoreInputSC)
    (hList : OddTranspListBundle) (hIn : OrthReflParabolic) (h1 : W16One G)
    (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (hm : 2 < mBar M V₀ V c.cex.hyp.h6.elemAbelian) : False := by
  have hn := c.one_le_mQuot
  by_cases h : E3.mQuot V (U ⊔ V₀) = 1
  · exact c.false_of_mQuot_eq_one h1 h5 h15 hS h hm
  · exact c.false_of_two_le_mQuot hTim
      (CFSG.LocalAnalysis.WeakClosure81.SevenK.twoConjugateGeneration_of_suzukiSubgroupInput
          LieType.SuzukiSubgroups.suzukiSubgroupInput_holds) hCore hList hIn kFacts1234_holds
      h1 h5 h15 hS (by omega)

theorem w16ClosingGt2_of_inputs (hTim : TimmesfeldTIRootInput)
    (hCore : OddTranspositionCoreInputSC) (hList : OddTranspListBundle)
    (hIn : OrthReflParabolic) (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) :
    W16ClosingGt2 G :=
  fun hS _ _ _ _ _ _ _ _ _ c hm =>
    (c.false_of_two_lt_mBar hTim hCore hList hIn h1 h5 h15 hS hm).elim

end Certified

end CFSG.LocalAnalysis.WeakClosure81
