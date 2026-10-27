module

public import CFSG.LocalAnalysis.StandardType.GGNbrU63StepOne
public import CFSG.LocalAnalysis.StandardType.GGNbrU63StepTwo

public section

namespace CFSG.StandardType

theorem ggUnitDvd63NbrRankInput_holds
    (hL : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) : GGUnitDvd63NbrRankInput := by
  intro G _ _ p B Bs x L D J hcfg y K hnb hN hM
  have hp3 : p = 3 :=
    Line63.H5.prime_eq_three_of_innerDiagOnLab (NbrU63.innerDiagOnLab_of_label hM)
  subst hp3
  by_contra hlt
  push Not at hlt
  exact NbrU63.nbrU63_stepTwo hL hcfg
    (hPJ _ _ _ _ _ _ _ hcfg.1 hcfg.2.2) hnb hN hM hlt
    (NbrU63.nbrU63_stepOne hcfg hnb hN hM hlt)

end CFSG.StandardType

end
