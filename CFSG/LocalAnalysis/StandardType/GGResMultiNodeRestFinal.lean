module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7A3Final
public import CFSG.LocalAnalysis.StandardType.GGResKOnlySingularA
import CFSG.LocalAnalysis.StandardType.GGHdRo7DFinal

public section

namespace CFSG.StandardType

theorem ggResMultiNodeRestInput_of_two_three
    (hX : GGResXDichotomyInput)
    (hJ : GGTBJInputR) (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hKG : GGReflClassLargeInput') (h2 : GGResMultiNodeRestTwoOnlyOutsideRowsInput)
    (h3 : GGResMultiNodeRestThreeOutsideRowsInput) : GGResMultiNodeRestInput :=
  ggResMultiNodeRestInput_of_reserved_two_three
    (HdRo7A3.ggResSUCorank3Input_proved hX hJ hRig hLB hKG)
    (HdRo7D.ggResDCorank2Input_proved hX hJ hRig hLB hKG)
    (ggResMultiNodeRestTwoOnlyOutsideRowsInput_of_L (by
      intro G _ _ p B Bs x L D J y K hH _ hF hS hE ⟨hDL, hrest⟩
      exact h2 G p B Bs x L D J y K hH hF hS hE ⟨Or.inl hDL, hrest⟩)) h3

end CFSG.StandardType
