module

public import CFSG.LocalAnalysis.UniquenessCase.UC9R96Comm
public import CFSG.LocalAnalysis.UniquenessCase.UC9R96I9
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R92b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC9R96

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r9_6At7_of_inputs (hK32 : UCK.K32) (hK461 : UCK.K461)
    (hK462 : UCK.K462) (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (D : Data G) :
    R9_6At7 D := by
  intro Y H D₃ hyp hne hC h7 hN
  obtain ⟨h92L, h92S⟩ := F09.r92_of_inputs hK32 hSch D Y H D₃ hyp hne
  exact (Std96.toCore ⟨hyp, hne, hC, h7⟩).false_of_shape92 hN hyp hK461 hK462 hSch h92L h92S

end CFSG.LocalAnalysis.UniquenessCase.UC9R96
