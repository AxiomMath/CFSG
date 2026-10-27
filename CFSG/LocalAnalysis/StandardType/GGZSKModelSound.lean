module

public import Certificates.Certificate709542

public section

namespace CFSG.StandardType.ZS

theorem exists_hsFive_model :
    ∃ t : Fin 5 → ↥(model .K5), HSFiveRel t ∧ Subgroup.closure (Set.range t) = ⊤ ∧
      ExcRow.K5.ord ≤ Nat.card (model .K5) ∧ IsReflMat (t 0).1 :=
  Certificates.certificate709542.1

theorem exists_hsSix_model :
    ∃ t : Fin 6 → ↥(model .K6), HSSixRel t ∧ Subgroup.closure (Set.range t) = ⊤ ∧
      ExcRow.K6.ord ≤ Nat.card (model .K6) ∧ IsReflMat (t 0).1 :=
  Certificates.certificate709542.2

end CFSG.StandardType.ZS

end
