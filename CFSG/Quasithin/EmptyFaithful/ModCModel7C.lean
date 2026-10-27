module

public import CFSG.Quasithin.EmptyFaithful.ModCModel7Defs

public section

namespace CFSG.Quasithin.ModC

open Equiv Equiv.Perm CFSG.Quasithin.G6

namespace M7

set_option maxRecDepth 100000

theorem g_analysis : ∀ g : Perm (Fin 7), permAct 7 g a = a → g ^ 3 = 1 → ∀ v ∈ [w, a * w],
    permAct 7 g v ≠ v → permAct 7 g v ≠ a * v → (join3F a v g).card = 8 ∨ x ∈ join3F a v g := by
  decide +kernel

theorem g_tri : ∀ g : Perm (Fin 7), GTri g → (g 6).val < 4 := by
  decide +kernel

end M7

end CFSG.Quasithin.ModC
