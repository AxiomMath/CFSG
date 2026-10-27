module

public import Certificates.Data.SmithB45HM22Flag
import all Certificates.Data.SmithB45HM22Flag
import Certificates.Kernel.HM22Flag.Checks
import CFSG.Certificates.Kernel.HM22FlagSound

public section

open CFSG.Quasithin.HM22

namespace CertificateChecks.Batch260415

open CFSG.Quasithin.HM22

private theorem flag3a : flagCheck3a = true := by
  decide +kernel

private theorem flag3b : flagCheck3b = true := by
  decide +kernel

private theorem flag9 : flagCheck9 = true := by
  have hP : flagP9.length = 198 := by decide +kernel
  have hPi : flagPi9.length = 198 := by decide +kernel
  have hns : ∀ i < flagNs9.length - 1, nsF flagNs9 (i + 1) ≤ 198 := by decide +kernel
  unfold flagCheck9
  exact CFSG.KC.HM22Flag.flagOK_of_cols hP hPi hns
    (fun j hj => CFSG.KC.HM22Flag.all_of_chunks HM22Flag.ch260415iAll j (by omega))
    (fun j hj => CFSG.KC.HM22Flag.all_of_chunks HM22Flag.ch260415aAll j (by omega))
    (fun j hj => CFSG.KC.HM22Flag.all_of_chunks HM22Flag.ch260415bAll j (by omega))

end CertificateChecks.Batch260415

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.HM22 in
theorem certificate260415 : flagCheck3a = true ∧ flagCheck3b = true ∧ flagCheck9 = true :=
  ⟨CertificateChecks.Batch260415.flag3a, CertificateChecks.Batch260415.flag3b, CertificateChecks.Batch260415.flag9⟩

end Certificates
