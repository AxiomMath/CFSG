module

public import CFSG.LocalAnalysis.StandardType.GGTWExt2Defs

public section

namespace CFSG.StandardType

theorem ggTWExt2All_D {n : ℕ} (hn : n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 8 ∨ n = 9) :
    GGTWExt2All (ggCoxeterMatrixD n) := by
  rcases hn with rfl | rfl | rfl | rfl | rfl <;>
    exact ggTWExt2All_of_check (by decide +kernel)

end CFSG.StandardType

end
