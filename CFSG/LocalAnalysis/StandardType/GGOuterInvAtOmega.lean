module

public import CFSG.LocalAnalysis.StandardType.GGGraphInvInputAtOmega
public import CFSG.LocalAnalysis.StandardType.GGO2CentralizerG0Holds

public section

namespace CFSG.StandardType

theorem ggOuterInvAt_POmegaPlus
    : GGOuterInvAt .POmegaPlus :=
  ggOuterInvAt_of_graphInv (ggPsiDiagInnerAt_of_ggInnerTag .POmegaPlus (Or.inr (Or.inl rfl)))
    (ggO2CentralizerG0At_holds .POmegaPlus) ggGraphInvInputAt_POmegaPlus

theorem ggOuterInvAt_POmegaMinus
    : GGOuterInvAt .POmegaMinus :=
  ggOuterInvAt_of_graphInv
    (ggPsiDiagInnerAt_of_ggInnerTag .POmegaMinus (Or.inr (Or.inr (Or.inl rfl))))
    (ggO2CentralizerG0At_holds .POmegaMinus) ggGraphInvInputAt_POmegaMinus

end CFSG.StandardType
