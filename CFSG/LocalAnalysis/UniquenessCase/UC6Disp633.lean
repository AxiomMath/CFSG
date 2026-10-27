module

public import CFSG.LocalAnalysis.UniquenessCase.UC6L34Aut
public import CFSG.LocalAnalysis.UniquenessCase.UC6M11Aut
public import CFSG.LocalAnalysis.UniquenessCase.UC6A10Kernels
public import CFSG.LocalAnalysis.UniquenessCase.UC6TitsKernels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor IsAlt)

section Disp633


namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

theorem kc633_of_L620 (hL : m.L620) : m.KC633 := by
  obtain ⟨h620, hlist⟩ := hL
  rcases hlist with hL2 | ⟨hr3, hM | hL34⟩ | ⟨hr5, hT | hA⟩
  · exact (m.kernels633_of_lieModel h620 hL2).1
  · exact m.kc633_of_m11 h620 hr3 hM
  · exact m.kc633_of_l34 h620 hr3 hL34
  · exact m.kc633_of_tits h620 hr5 hT
  · exact m.kc633_of_A10 h620 hr5 hA

theorem kn633_of_L620 (hL : m.L620) : m.KN633 := by
  obtain ⟨h620, hlist⟩ := hL
  rcases hlist with hL2 | ⟨hr3, hM | hL34⟩ | ⟨hr5, hT | hA⟩
  · exact (m.kernels633_of_lieModel h620 hL2).2.1
  · exact m.kn633_of_m11 h620 hr3 hM
  · exact m.kn633_of_l34 h620 hr3 hL34
  · exact m.kn633_of_tits h620 hr5 hT
  · exact m.kn633_of_A10 h620 hr5 hA

theorem kinv633_of_L620 (hL : m.L620) : m.KInv633 := by
  obtain ⟨h620, hlist⟩ := hL
  rcases hlist with hL2 | ⟨hr3, hM | hL34⟩ | ⟨hr5, hT | hA⟩
  · exact (m.kernels633_of_lieModel h620 hL2).2.2
  · exact m.kinv633_of_m11 h620 hr3 hM
  · exact m.kinv633_of_l34 h620 hr3 hL34
  · exact m.kinv633_of_tits h620 hr5 hT
  · exact m.kinv633_of_A10 h620 hr5 hA

end Mz614

end Disp633

end CFSG.LocalAnalysis.UniquenessCase.UC6
