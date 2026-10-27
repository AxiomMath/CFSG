module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Defs
import CFSG.Quasithin.Background.HatA6Norm

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

theorem gapThreeA6Normalizer_holds : GapThreeA6Normalizer := by
  intro W _ _ hW2 K hK _ hW
  obtain ⟨hq, hZ, ⟨e⟩⟩ := hK
  exact CFSG.Quasithin.HatA6.exists_normalizer_hom_perm hW2 hW hq.1 hZ e

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

end
