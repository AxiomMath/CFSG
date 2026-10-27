module

public import CFSG.Quasithin.EmptyFaithful.ModCModel7Defs

public section

namespace CFSG.Quasithin.ModC

open Equiv Equiv.Perm CFSG.Quasithin.G6

namespace M7

set_option maxRecDepth 100000

theorem classify : ∀ z : PermMod 7, CondZ z → ∀ v : PermMod 7, CondV z v → Concl z v := by
  decide +kernel

end M7

end CFSG.Quasithin.ModC
