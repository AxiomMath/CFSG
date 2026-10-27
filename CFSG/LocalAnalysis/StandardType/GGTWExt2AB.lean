module

public import CFSG.LocalAnalysis.StandardType.GGTWExt2Defs

public section

namespace CFSG.StandardType

theorem ggTWExt2All_A {n : ℕ} (hn : n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 8 ∨ n = 9) :
    GGTWExt2All (CoxeterMatrix.A n) := by
  rcases hn with rfl | rfl | rfl | rfl | rfl <;>
    exact ggTWExt2All_of_check (by decide +kernel)

theorem ggTWExt2All_B {n : ℕ} (hn : n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 8 ∨ n = 9) :
    GGTWExt2All (CoxeterMatrix.B n) := by
  rcases hn with rfl | rfl | rfl | rfl | rfl <;>
    exact ggTWExt2All_of_check (by decide +kernel)

end CFSG.StandardType

end
