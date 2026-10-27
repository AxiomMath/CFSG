module

public import CFSG.Milestones.ASVolI.F48.Small.AutChartInputs
import Certificates.Kernel.AutChart.U42B
import CFSG.Certificates.Kernel.DcKParse

public section

open CFSG CFSG.ASVolI

namespace Certificates

open CertificateChecks

open CFSG CFSG.ASVolI in
theorem certificate7544 : burnsideF48s_autc_u42_checkMem () = true ∧ burnsideF48s_autc_u42_checkB () = true := by
  have hW : burnsideF48s_autc_u42BW () = KernelAutChart.wordsL KernelAutChart.U42B.chars := by
    rw [burnsideF48s_autc_u42BW, burnsideF48s_autc_words, KernelAutChart.U42B.eq,
      CFSG.KC.DcK.comma_eq, CFSG.KC.Str.splitOn_ofList, KernelAutChart.wordsL,
      CFSG.KC.DcK.splitGo_nil, List.map_map]
    congr 1
    funext l
    simp [burnsideF48s_autc_word]
  refine ⟨KernelAutChart.checkMem, ?_⟩
  rw [burnsideF48s_autc_u42_checkB, hW]
  exact KernelAutChart.checkB_list

end Certificates
