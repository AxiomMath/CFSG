module

public import CFSG.CGT.T75JM.PCheckInputs
import Certificates.Kernel.T75JM.N0KGlue
import Certificates.Kernel.T75JM.PCheckKChecks
import CFSG.Certificates.Kernel.T75JM.PCheckKSound

public section

open CFSG.CGT.T75JM CFSG.KC.N0K

namespace Certificates

open CFSG.CosetTable CFSG.CGT.T75JM in
theorem certificate14983 : (eMulCheck = true) ∧ (eInjCheck = true) ∧
    (∀ n : PG 6 rels6, (∀ j : Fin 3, n * val6 (vExp (eW (Pi.single j 1))) =
      val6 (vExp (eW (Pi.single j 1))) * n) → ∃ c : V3, n = val6 (vExp (eW c))) ∧
    (eTorsCheck = true) ∧
    (actVCheck = true) ∧ (actGCheck = true) ∧ (thetaCheck = true) ∧ (d8Check = true) ∧
    (∀ d : DihedralGroup 4, (∀ c, glAct (matD mS mR d) c = c) → d = 1) ∧
    FinCheck mv pRs pEw pWords := by
  obtain ⟨h1, h2, h4, h5, h6, h7, h8⟩ := pChecks_of letterRd_LP pOk_ok
  exact ⟨h1, h2, e_cent_of letterRd_LP n0Inv_ok n0k_ok eCent_ok, h4, h5, h6, h7, h8, d8_dist_ok,
    finCheck_of aff_ok tr_ok fin_ok⟩

end Certificates
