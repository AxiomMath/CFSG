module

public import CFSG.Quasithin.EmptyFaithful.S153G93DCases
public import CFSG.Quasithin.EmptyFaithful.S153G93DCovG2Model

public section

namespace CFSG.Quasithin

namespace S153G93D

namespace CovG2

open CFSG.Open

theorem covG2Der_holds :
    CovG2Der := by
  intro W _ _ J hJ w _
  obtain ⟨K, instK, instF, hK, π, hπ⟩ := hJ
  have hK2 : Nat.card K = 2 := by simpa using hK
  exact S153EB6.exists_order_three_fix _ J π hπ
    (model_order_three hK2 le_rfl) w

theorem covG2One_holds :
    CovG2One := by
  intro W _ _ J hJ w _
  obtain ⟨K, instK, instF, hK, π, hπ⟩ := hJ
  have hK2 : Nat.card K = 2 := by simpa using hK
  exact S153EB6.exists_order_three_fix _ J π hπ
    (model_order_three hK2 (Subgroup.commutator_le_self _)) w

end CovG2

end S153G93D

end CFSG.Quasithin
