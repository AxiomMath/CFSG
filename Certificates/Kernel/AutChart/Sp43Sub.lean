module

public import Certificates.Data.Kernel.F48Small.AutC
public import Certificates.Kernel.AutChart.Sp43Str
public import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelAutChart

open CFSG.ASVolI CFSG.KC.F48S CFSG.KC.LQT.L

@[expose] noncomputable def sp43G : List ℕ := (burnsideF48s_autc_sp43gl ()).map encL

@[expose] noncomputable def sp43Gi : List ℕ := (burnsideF48s_autc_sp43gli ()).map encL

@[expose] noncomputable def sp43C (cs : List Char) : List ℕ := (autcWords cs).map (evK 45 sp43G sp43Gi)

theorem ch7545rel : burnsideF48s_autc_sp43_checkRel () = true := by
  decide +kernel

theorem ch7545let : autcLetOK (burnsideF48s_autc_sp43gl ()) (burnsideF48s_autc_sp43gli ()) = true := by
  decide +kernel

theorem ch7545headB : autcHead (autcWords Sp43B.chars) [0, 1, 4] 324 = true := by
  decide +kernel

theorem ch7545head1 : autcHead (autcWords Sp43P1.chars) [0, 1, 2, 4] 1296 = true := by
  decide +kernel

theorem ch7545head2 : autcHead (autcWords Sp43P2.chars) [0, 1, 3, 4] 1296 = true := by
  decide +kernel

theorem ch7545groupB : groupK 45 (sp43C Sp43B.chars) ([0, 1, 4].map (getK sp43G)) = true := by
  quickRfl

theorem ch7545group1 : groupK 45 (sp43C Sp43P1.chars) ([0, 1, 2, 4].map (getK sp43G)) = true := by
  quickRfl

theorem ch7545group2 : groupK 45 (sp43C Sp43P2.chars) ([0, 1, 3, 4].map (getK sp43G)) = true := by
  quickRfl

theorem ch7545inf :
    autcInfK (sp43C Sp43P1.chars) (setT (sp43C Sp43P2.chars)) (setT (sp43C Sp43B.chars)) = true := by
  quickRfl

end CertificateChecks.KernelAutChart
