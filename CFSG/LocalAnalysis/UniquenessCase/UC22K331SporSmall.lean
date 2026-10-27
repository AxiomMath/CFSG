module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K331Fams
import CFSG.LocalAnalysis.UniquenessCase.UC22K331SporLat
import CFSG.LocalAnalysis.UniquenessCase.UC22K331SporM23

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open CFSG.Blueprint.NativeSporadic (Carrier)

theorem k331_sporSmall
    (hbr : ∀ s : TauCeti.SporadicName, Nonempty (Carrier s ≃* s.Group)) :
    K331Fam K331SporSmall := by
  intro i hi
  cases i with
  | sporadic s =>
    rcases hi with rfl | rfl | rfl | rfl
    · exact k331Idx_j2 (hbr _)
    · exact k331Idx_m22 (hbr _)
    · exact k331Idx_m23 (hbr _)
    · exact k331Idx_hs (hbr _)
  | _ => exact hi.elim

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
