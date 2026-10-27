module

public import CFSG.Milestones.ASVolI.F48.Small.AutChartInputs
public import Certificates.Kernel.SporSch.Th.GenStr
public import Certificates.Data.Kernel.DcK
public import Mathlib

public section

#kss_strof CertificateChecks.KernelAutChart.U42B CFSG.ASVolI.burnsideF48s_autc_u42BStr

namespace CertificateChecks.KernelAutChart

open CFSG.ASVolI

@[expose] def wordsL (cs : List Char) : List (List (Fin 5 × Bool)) :=
  (CFSG.KC.DcK.splitGo ',' cs []).map fun l => l.map burnsideF48s_autc_letter

theorem checkB_list : burnsideF48s_autc_groupB (burnsideF48s_autc_u42gl ())
    (burnsideF48s_autc_u42gli ()) [0, 1, 4] (wordsL U42B.chars) 384 = true := by
  decide +kernel

theorem checkMem : burnsideF48s_autc_u42_checkMem () = true := by
  decide +kernel

end CertificateChecks.KernelAutChart
