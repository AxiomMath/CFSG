module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K35OmP5
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35Holds
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.StrongThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallOutPPrime
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588E6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

section OfKFacts


theorem K35Ω_of_kfacts
    (hG3 : CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3StronglyThreeEmbeddedPlus)
    (hSI : CFSG.AGLEmbedding.KFactSmallIdent) (hTor : CFSG.AGLEmbedding.KFactOneLieTorus)
    (hOutP : CFSG.AGLEmbedding.KFactSmallOutPPrime)
    (hK2 : CFSG.LocalAnalysis.RankThreeTheoremC.StronglyEmbeddedCyclicOuterKFact)
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (CFSG.Blueprint.NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group)) :
    K35Ω := by
  intro X _ _ hX p hp hp2 hopp hO N hN S B hS hBS hB hBcard hΩ hBc
  by_cases h3 : p = 3
  · exact k35Ω_three hG3 hbr hX h3 hopp hO hN hS hBS hB hBcard hΩ hBc
  · have h4 : p ≠ 4 := by
      rintro rfl
      norm_num at hp
    have hp5 : 5 ≤ p := by
      have := hp.two_le
      omega
    exact k35Ω_five hSI hTor hOutP hK2 hbr hX hp hp5 hopp hO hN hS hBS hB hBcard hΩ hBc

end OfKFacts

section Holds


theorem K35Ω_holds
    : K35Ω :=
  K35Ω_of_kfacts CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
    kFactSmallIdent_holds kFactOneLieTorus_holds
    (CFSG.AGLEmbedding.kFactSmallOutPPrime_of_smallIdent kFactSmallIdent_holds)
    stronglyEmbeddedCyclicOuter_holds CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group

end Holds

end CFSG.LocalAnalysis.UniquenessCase.UCK
