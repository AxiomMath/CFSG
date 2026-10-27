module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Assembly
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35Holds
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.J4Eleven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive

section Certificates


theorem stronglyEmbeddedFive_holds
    : StronglyEmbeddedFive := by
  obtain ⟨eM⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  obtain ⟨eJ⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  have hM : Nat.card (TauCeti.CFSGIndex.sporadic .McL).Group = 898128000 :=
    (Nat.card_congr eM.toEquiv).symm.trans CFSG.Sporadic.McL.card_McL
  have hJ : Nat.card (TauCeti.CFSGIndex.sporadic .J4).Group = 86775571046077562880 :=
    (Nat.card_congr eJ.toEquiv).symm.trans CFSG.Sporadic.J4.card_J4
  refine stronglyEmbeddedFive_of_kFacts UCK.kFactSmallIdent_holds UCK.kFactOneLieIdent_holds
    UCK.stronglyEmbeddedCyclicOuter_holds CFSG.AGLEmbeddingD2.d2HeisLocalAt_mcl
    CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4 ?_ ?_ ?_ ?_
  · rw [hM]
    exact Nat.dvd_of_mod_eq_zero (by norm_num)
  · rw [hJ]
    exact Nat.dvd_of_mod_eq_zero (by norm_num)
  · rw [hJ]
    exact fun h => absurd (Nat.mod_eq_zero_of_dvd h) (by norm_num)
  · let eC : Blueprint.NativeSporadic.Carrier .J4 ≃* Blueprint.NativeSporadic.J4 :=
      MulEquiv.refl _
    exact (Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      (eC.trans eJ)).toEquiv).symm.trans CFSG.AGLEmbedding.card_outer_J4

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive
