module

public import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeOpenDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeNineTP
public import CFSG.LocalAnalysis.StandardType.GGQ2TablePAtL
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CuKPlacement
import CFSG.LocalAnalysis.StandardType.GGQ2FrameSmall
import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalPlacementHolds

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.GGQ2Frame

theorem ggQ2TwoNodeOpen_of_cells (h6 : GGQ2S08TNCell (GGQ2S08PosTwA 6))
    (h9 : GGQ2S08TN9RestCell) (hA : GGQ2S08TNCellK GGQ2S08PosASmall) : GGQ2TwoNodeOpenInput := by
  intro G _ _ p _ hp B Bs x L D J hS hI1 y K hnb hpos _ _ _ h9L h9K
  rcases hpos with ⟨h | h, hx⟩ | ⟨h | h | h, hy⟩
  · exact h6 hp hS hI1 hnb (Or.inl ⟨h, hx⟩)
  · exact h9 hp hS hI1 hnb (Or.inl ⟨h, hx⟩) h9L h9K
  · exact h6 hp hS hI1 hnb (Or.inr ⟨h, hy⟩)
  · exact h9 hp hS hI1 hnb (Or.inr ⟨h, hy⟩) h9L h9K
  · exact hA hp hS hI1 hnb h hy

theorem ggQ2TwoNodeOpen_of_leaves
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hNC : GGLNoncyclicInput)
    (h5 : GGQTwoCentralizerInput) (hK : GGReflClassOmegaInput) (hT : GGTPNTransferBNoCorners)
    (hB3 : GGK0ExcB3) (hQ : GGPCompCentQuasisimple fun _ => True)
    (hplEx : PlacementCoreInputOn ExceptionalLabel (catalogueOf classicalCatalogue excCatalogue)) :
    GGQ2TwoNodeOpenInput :=
  ggQ2TwoNodeOpen_of_cells (ggQ2s08_tn6_of_leaves hLB hP hNC h5 hK hT hB3 hQ)
    (ggQ2s08_tn9Rest_of_leaves hLB hP hNC h5 hK hT hB3 hQ)
    (GGQ2S08Split.ggQ2s08_cuKA_of_placement ggLabelRigidInput_holds hLB hP
      (placementCoreInputOn_classical_holds excCatalogue) hplEx (placementCoreInputOn_small _))

end CFSG.StandardType

end
