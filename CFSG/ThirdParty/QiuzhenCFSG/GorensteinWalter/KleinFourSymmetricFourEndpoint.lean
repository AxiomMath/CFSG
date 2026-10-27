module

public import Mathlib.Data.Fintype.Perm
public meta import Mathlib.Data.Fintype.Perm
public import Mathlib.Algebra.Group.End
public meta import Mathlib.Algebra.Group.End
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

public abbrev Perm4OrderThree := {a : Equiv.Perm (Fin 4) // a ^ 3 = 1}
public abbrev Perm4Involution := {v : Equiv.Perm (Fin 4) // v * v = 1}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- In `S₄`, no involution centralizes an order-three element. -/
public theorem no_involution_centralizes_order_three_perm_four :
    ∀ a : Perm4OrderThree, ∀ v : Perm4Involution,
      (a : Equiv.Perm (Fin 4)) ≠ 1 →
      (v : Equiv.Perm (Fin 4)) * (a : Equiv.Perm (Fin 4)) =
        (a : Equiv.Perm (Fin 4)) * (v : Equiv.Perm (Fin 4)) →
      (v : Equiv.Perm (Fin 4)) = 1 := by
  decide

end CFSG.GorensteinWalter
