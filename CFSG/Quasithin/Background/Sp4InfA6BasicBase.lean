
module

public import CFSG.Quasithin.Background.Sp4InfA6BasicInputs

@[expose] public section

namespace CFSG.Quasithin

namespace Sp4Inf

open Equiv Pointwise

theorem mem_q1 (x : Perm (Fin 6)) : x ∈ q1 ↔ bq1 x = true := by
  simp [q1, bq1, MulAction.mem_stabilizer_iff, Perm.mem_alternatingGroup]

theorem mem_q2 (x : Perm (Fin 6)) : x ∈ q2 ↔ bq2 x = true := by
  simp [q2, bq2, MulAction.mem_stabilizer_iff, Perm.mem_alternatingGroup]

theorem mem_s0 (x : Perm (Fin 6)) : x ∈ s0 ↔ bs0 x = true := by
  simp [s0, bs0, mem_q1, mem_q2]

theorem q1_le_alt : q1 ≤ alternatingGroup (Fin 6) := inf_le_right

theorem q2_le_alt : q2 ≤ alternatingGroup (Fin 6) := inf_le_right

end Sp4Inf

end CFSG.Quasithin
