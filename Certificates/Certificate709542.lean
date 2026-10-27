module

public import Certificates.Kernel.HSMK.Glue

public section

public section

namespace Certificates

open CFSG.StandardType.ZS in
theorem certificate709542 :
    (∃ t : Fin 5 → ↥(model .K5), HSFiveRel t ∧ Subgroup.closure (Set.range t) = ⊤ ∧
      ExcRow.K5.ord ≤ Nat.card (model .K5) ∧ IsReflMat (t 0).1) ∧
    (∃ t : Fin 6 → ↥(model .K6), HSSixRel t ∧ Subgroup.closure (Set.range t) = ⊤ ∧
      ExcRow.K6.ord ≤ Nat.card (model .K6) ∧ IsReflMat (t 0).1) :=
  ⟨CFSG.StandardType.ZS.HSMK.hsmk_five, CFSG.StandardType.ZS.HSMK.hsmk_six⟩

end Certificates

end

end
