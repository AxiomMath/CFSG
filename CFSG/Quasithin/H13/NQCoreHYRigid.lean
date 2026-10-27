module

public import CFSG.Quasithin.H13.NQCoreHYSingle
public import CFSG.Quasithin.H13.A7FiveModelRigid

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open

theorem stmtFiveModelLocalChainRigid_holds :
    StmtFiveModelLocalChainRigid := by
  intro G _ _ T D B hT hDp hTD hBD hB1 hBp hTB h5
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : ((hT.1.toSylow hT.2 : Sylow 2 G) : Subgroup G) = T := IsPGroup.toSylow_coe hT.1 hT.2
  exact A7.local_chain_eq_of_QT13Five (hT.1.toSylow hT.2) hDp (by rw [hc]; exact hTD) hBD hB1
    hBp (by rw [hc]; exact hTB) h5

end CFSG.Quasithin.H13.NQCore
