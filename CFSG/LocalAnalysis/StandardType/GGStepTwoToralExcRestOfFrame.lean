module

public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralSmallOfFrame
public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralIndexOfFrame
public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertAll
public import Certificates.Certificate946001
public import Certificates.Certificate946002
public import Certificates.Certificate946003
public import Certificates.Certificate946004
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoToralExcSixE
public import CFSG.LocalAnalysis.StandardType.GGExcKGRankTwE6Holds
public import CFSG.LocalAnalysis.StandardType.GGExcLeviRankMax

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Regime

theorem ggExcRegimeInput_holds : GGExcRegimeInput :=
  ggExcRegimeInput_of_known (ggExcKGRank_of_twE6 ggExcKGRankTwE6_holds) ggExcKGBorelTits_holds

end Regime

section Frame

theorem ggStepTwoToralWitnessSmallOn_of_frame (hF : GGExcKGToralFrame) {t : StatedLieTag}
    (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) :
    GGStepTwoToralWitnessSmallOn t :=
  ggStepTwoToralWitnessSmallOn_of_frameSpec hF ggExcRegimeInput_holds
    (StepTwoToralCert.certAll_of_specs Certificates.certificate946001
      Certificates.certificate946002 Certificates.certificate946003
      Certificates.certificate946004) ht

theorem ggStepTwoToralExcRest_of_frame (hF : GGExcKGToralFrame) : GGStepTwoToralExcRest :=
  ⟨ggStepTwoToralWitnessExcRestOn_of_index_small
      (ggStepTwoExcIndexNonsplitOn_of_frame hF ggExcRegimeInput_holds (Or.inl rfl))
      (ggStepTwoToralWitnessSmallOn_of_frame hF (Or.inl rfl)),
    ggStepTwoToralWitnessExcRestOn_of_index_small
      (ggStepTwoExcIndexNonsplitOn_of_frame hF ggExcRegimeInput_holds (Or.inr (Or.inl rfl)))
      (ggStepTwoToralWitnessSmallOn_of_frame hF (Or.inr (Or.inl rfl))),
    ggStepTwoToralWitnessExcRestOn_of_index_small
      (ggStepTwoExcIndexNonsplitOn_of_frame hF ggExcRegimeInput_holds
        (Or.inr (Or.inr (Or.inl rfl))))
      (ggStepTwoToralWitnessSmallOn_of_frame hF (Or.inr (Or.inr (Or.inl rfl)))),
    ggStepTwoToralWitnessExcRestOn_of_index_small
      (ggStepTwoExcIndexNonsplitOn_of_frame hF ggExcRegimeInput_holds
        (Or.inr (Or.inr (Or.inr rfl))))
      (ggStepTwoToralWitnessSmallOn_of_frame hF (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
    ggStepTwoToralWitnessOn_of_index_small
      (ggStepTwoExcIndexOn_twistedE6_of_frame hF ggExcRegimeInput_holds)
      (ggStepTwoToralWitnessSmallOn_of_frame hF (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))⟩

end Frame

end CFSG.StandardType
