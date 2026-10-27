module

public import CFSG.Sporadic.Th.Certificate

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3

theorem ctuc_Th_full_central_involution_centralizer :
    Subgroup.centralizer {a} = M ∧ Nat.card (Subgroup.centralizer {a} : Subgroup J) = 92897280 ∧
    CFSG.pCore 2 (Subgroup.centralizer {a} : Subgroup J) =
      Q.subgroupOf (Subgroup.centralizer {a}) ∧
    Subgroup.centralizer (Q : Set J) ⊓ Subgroup.centralizer {a} = Subgroup.zpowers a := by
  have h := centralizer_a_eq_M_kernel
  refine ⟨h, by rw [h, card_M], ?_, by rw [h, centralizer_Q_inf_M, z_eq_a]⟩
  rw [h]
  exact pCore_M

end CFSG.Sporadic.ThSchreier
