module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenBig
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenSmallTri
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.Main
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12b
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosure

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (W3Lem711)

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

theorem seven_eleven (hTim : TimmesfeldTIRootInput) (hGen : TwoConjugateGeneration)
    (hA6 : SevenElevenASixInput G) (hCore : OddTranspositionCoreInputSC)
    (hList : OddTranspListBundle)
    (h772 : SevenSevenTwoInput G)
    (hIn : OrthReflParabolic) (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ) :
    (∀ u ∈ dSet V H E, ∀ v ∈ dSet V H E, ∃ k ∈ kSub V H E, u = k * v * k⁻¹) ∧
      SevenElevenAlt X (barSub (kSub V H E) φ V) := by
  rcases (two_le_card_barSub h hφ).eq_or_lt with h2 | hbig
  · exact seven_eleven_small hCore hList (OddCentral.sevenSevenOddCentral G) h772 hIn h hφ h2.symm
  · exact seven_eleven_big hTim hGen hA6 h hφ hbig

end CFSG.LocalAnalysis.WeakClosure81
