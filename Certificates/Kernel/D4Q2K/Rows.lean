module

public import Certificates.Data.Kernel.D4Q2K.Defs
public import Certificates.Kernel.D4Q2K.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4Q2K

open CFSG.KC.D4Q2K

theorem ch709441rw0 : rowsK D.pts (D.RF) (0) 280 = true := by
  quickRfl

theorem ch709441rw1 : rowsK D.pts (D.RF) (280) 280 = true := by
  quickRfl

theorem ch709441rw2 : rowsK D.pts (D.RF) (560) 280 = true := by
  quickRfl

theorem ch709441rw3 : rowsK D.pts (D.RF) (840) 280 = true := by
  quickRfl

theorem ch709441rw4 : rowsK D.pts (D.RF) (1120) 280 = true := by
  quickRfl

theorem ch709441rw5 : rowsK D.pts (D.RF) (1400) 280 = true := by
  quickRfl

theorem ch709441rw6 : rowsK D.pts (D.RF) (1680) 280 = true := by
  quickRfl

theorem ch709441rw7 : rowsK D.pts (D.RF) (1960) 280 = true := by
  quickRfl

theorem ch709441rw_negSelf : (!rowsK D.pts (fun i => Nat.lor (D.RF i) 1) 0 1) = true := by
  quickRfl

theorem ch709441rw_negShift : (!rowsK D.pts (fun i => D.RF (Nat.succ i)) 0 1) = true := by
  quickRfl

end CertificateChecks.KernelD4Q2K

end
