
module

public import CFSG.Sporadic.Schreier.J4SProfileNodeBase

public import CFSG.Sporadic.Schreier.J4SProfileCheck
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.Schreier.J4SProfile
public meta import CFSG.Sporadic.Schreier.J4SProfile
public import CFSG.Sporadic.Schreier.J4SSylowData
public meta import CFSG.Sporadic.Schreier.J4SSylowData
public import CFSG.Sporadic.J4.Local

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

theorem stepNF_lt {n e : ℕ} (hn : n < 2048) (he : e < 1024) :
    (stepNF (n, e)).1 < 2048 ∧ (stepNF (n, e)).2 < 1024 := by
  refine ⟨?_, (sq_all e he).1⟩
  have hb : ∀ j < 11, (elementColumns[e]!)[j]?.getD 0 < 2 ^ 11 := fun j hj => by
    rw [← getElem!_eq_getD']; exact (elem_all e he).2.1 j hj
  exact Nat.xor_lt_two_pow (by omega) (vecMulN_lt hb n)

end CFSG.Sporadic.J4Schreier
