module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.ZMod.Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

theorem d5_fixed_by_three : ∀ v : Fin 5 → ZMod 2, ∑ i, v i = 0 →
    ∃ σ : Equiv.Perm (Fin 5), σ ^ 3 = 1 ∧ σ ≠ 1 ∧ Equiv.Perm.sign σ = 1 ∧ ∀ i, v (σ i) = v i := by
  decide +kernel

end CFSG.Quasithin.Vol2.Ch10.SecC
