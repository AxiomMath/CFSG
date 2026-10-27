module

public import CFSG.CGT.T75M23.P7CheckInputs
import Certificates.Kernel.T75M23.N7KGlue
import Certificates.Kernel.T75M23.P7KChecks
import CFSG.Certificates.Kernel.T75M23.P7KSound

public section

open CFSG.CGT.T75M23 CFSG.KC.N7K CFSG.KC.TabWord.M23

namespace Certificates

open CFSG.CGT.T75M23 CFSG.CGT.T75JM in
theorem certificate271033 : (eMulCheck7 = true) ∧ (eInjCheck7 = true) ∧
    (∀ n : N7, (∀ j : Fin 3, n * n7 (vExp7 (eW7 (Pi.single j 1))) =
      n7 (vExp7 (eW7 (Pi.single j 1))) * n) → ∃ c : V3, n = n7 (vExp7 (eW7 c))) ∧
    (eTorsCheck7 = true) ∧ (actVCheck7 = true) ∧ (actGCheck7 = true) ∧ (thetaCheck7 = true) ∧
    (d0Check7 = true) ∧ (d8Check7 = true) ∧
    (∀ d : DihedralGroup 4, (∀ c, glAct (matD mS7 mR7 d) c = c) → d = 1) ∧
    FinCheck mv7 pRs7a pEw7 pWords7 ∧ FinCheck mv7 pRs7b pEw7 [pEw7 0] := by
  obtain ⟨h1, h2, h4, h5, h6, h7, h7', h8⟩ := pChecks_of letterRd_NL pOk_ok
  exact ⟨h1, h2, e_cent_of letterRd_NL n7InvCheck_eq_true n7RelCheck_eq_true n7k_ok eCent_ok,
    h4, h5, h6, h7, h7', h8, d8_dist_ok, finCheck_of aff_ok tr_ok fin_a_ok,
    finCheck_of aff_ok tr_ok fin_b_ok⟩

end Certificates
