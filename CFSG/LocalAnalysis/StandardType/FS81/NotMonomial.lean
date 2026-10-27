module

public import CFSG.LocalAnalysis.StandardType.FS81.Pieces
public import CFSG.LocalAnalysis.StandardType.FS81.MonoN0

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

theorem l1NotMonomial_holds : L1NotMonomial := by
  intro G _ _ b₀ K E r hr hstd B hB hfus hodd hI
  obtain ⟨-, -, -, -, -, hbig⟩ := hstd.2.1
  have hn : 4 ≤ r.n := by
    cases r with
    | D6 => decide
    | twD7 => decide
    | E7 => exact absurd rfl hr
  obtain ⟨hspan, hb0, -⟩ := hB
  subst hspan
  exact false_of_normalizer_mono hn B hb0 hfus hodd hbig hI.2

end CFSG.StandardType.FrameRoute.FS81
