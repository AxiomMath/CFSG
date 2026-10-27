module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcAmbModel
public import CFSG.LocalAnalysis.StandardType.GGQ2FrameSmall

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly GGQ2Frame

theorem ggQ2AmbModelInput_of_placements
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hplCl : PlacementInputOn ClassicalLabel (catalogueOf classicalCatalogue excCatalogue))
    (hplEx : PlacementInputOn ExceptionalLabel (catalogueOf classicalCatalogue excCatalogue)) :
    GGQ2AmbModelInput := by
  have hamb : AmbModelFromFrameInput (catalogueOf classicalCatalogue excCatalogue) :=
    ambModelFromFrameInput_excCatalogue hLB hP
  have hOnCl : GGQ2AmbModelOnAmb ClassicalLabel := ggQ2AmbModelOnAmb_of_placementOn hplCl hamb
  have hOnEx : GGQ2AmbModelOnAmb ExceptionalLabel := ggQ2AmbModelOnAmb_of_placementOn hplEx hamb
  have hOnSm : GGQ2AmbModelOnAmb SmallLabel :=
    ggQ2AmbModelOnAmb_of_placementOn (placementInputOn_small _) hamb
  intro G _ _ p B Bs x L D J hS hp hI1 hxL hpp hrow hno y K hnb hr1 hr2 hW
  obtain ⟨lab, hm⟩ := ggQ2_marking_with_label hS.1.2.2.2.2
  rcases label_cases lab with h | h | h
  · exact hOnCl hS hp hI1 hxL
      (largeEvenMarking_mono (fun lab' R _ I F θ hh => by rw [hh]; exact h) hm) hrow hno hnb hr1 hr2
      hW
  · exact hOnEx hS hp hI1 hxL
      (largeEvenMarking_mono (fun lab' R _ I F θ hh => by rw [hh]; exact h) hm) hrow hno hnb hr1 hr2
      hW
  · exact hOnSm hS hp hI1 hxL
      (largeEvenMarking_mono (fun lab' R _ I F θ hh => by rw [hh]; exact h) hm) hrow hno hnb hr1 hr2
      hW

end CFSG.StandardType

end
