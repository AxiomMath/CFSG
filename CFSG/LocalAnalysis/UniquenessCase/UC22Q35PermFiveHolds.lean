module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35K3Covers
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35ClassicalE
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35OmegaE
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35G2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

theorem kQ35PermFive_holds :
    KQ35PermFive :=
  kq35PermFive_of_covers (fun _ _ hK => Q35Natural.sp4_three_sylowPQMaximal hK)
    (fun _ _ hK => Q35Natural.sp4_five_sylowPQMaximal hK)
    (fun _ _ hK => Q35Natural.su4_three_sylowPQMaximal hK)
    (fun _ _ hK => Q35Omega7.omega7_three_sylowPQMaximal hK)
    (fun _ _ hK => Q35G2.g2_five_sylowPQMaximal hK)

end CFSG.LocalAnalysis.UniquenessCase.UC22
