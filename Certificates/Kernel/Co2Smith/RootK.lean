module

public import Certificates.Kernel.Co2Smith.RootDefs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

theorem rootPar_k : rootParK = true := by decide +kernel

theorem rootComm_k : rootCommK = true := by decide +kernel

theorem chart_k : chartK = true := by decide +kernel

theorem uOK_k : uOKK = true := by decide +kernel

theorem frame_k : frameK = true := by decide +kernel

open CFSG.KC.Co2InvS CFSG.KC.Co2Smith in
theorem root_neg : (!eqK (mulV (rootK 0 1) (rootK 0 1)) (rootK 0 1) && !mapsK uK 80 81 &&
    !commK alK gaK && !eqK (comm4K (rootK 0 1) (rootK 12 1)) (rootK 0 1)) = true := by
  decide +kernel

end CertificateChecks.KernelCo2Smith
