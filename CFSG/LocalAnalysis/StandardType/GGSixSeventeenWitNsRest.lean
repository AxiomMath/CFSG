module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitNsSL
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitRest

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Inputs

@[expose] def GGSixSeventeenWitnessRest7 : Prop :=
  GGSixSeventeenWitnessOn GGPSUNonsplit ∧ GGSixSeventeenWitnessOn GGPSpNonsplit ∧
    GGSixSeventeenWitnessOn (fun t _ _ _ => t = .POmegaPlus) ∧
    GGSixSeventeenWitnessOn (fun t _ _ _ => t = .POmegaMinus) ∧
    GGSixSeventeenE8SevenInput ∧ GGSixSeventeenRootWitnessInputFor GGExceptionalTag

theorem ggSixSeventeenWitnessRest7_of_rest6 (h : GGSixSeventeenWitnessRest6) :
    GGSixSeventeenWitnessRest7 :=
  h.2

end Inputs

section Wiring

theorem ggSixSeventeenWitnessRest6_of_rest7 (h : GGSixSeventeenWitnessRest7) :
    GGSixSeventeenWitnessRest6 :=
  ⟨ggSixSeventeenWitnessOn_PSLNonsplit, h⟩

theorem ggSixSeventeenWitnessInput_of_rest7 (h : GGSixSeventeenWitnessRest7) :
    GGSixSeventeenWitnessInputFor fun _ => True :=
  ggSixSeventeenWitnessInput_of_rest6 (ggSixSeventeenWitnessRest6_of_rest7 h)

end Wiring

end CFSG.StandardType
