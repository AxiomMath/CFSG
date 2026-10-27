module

public import Certificates.Data.Kernel.AS91K42
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelAS91K42

open Certificates.Kernel.AS91K42 Certificates.Kernel.HJ12K CFSG.KC.Mat12P
  CFSG.Quasithin.H13.AS91.Two

theorem ch89401_q0 : q0OK = true := by quickRfl

theorem ch89401_o1 : orbOK gamF 3 o1Mask = true := by quickRfl

theorem ch89401_o2 : orbOK gamF 5 o2Mask = true := by quickRfl

theorem ch89401_o3 : orbOK gamF 1 q0M = true := by quickRfl

theorem ch89401_inv : invK = true := by quickRfl

theorem ch89401_part : partK = true := by quickRfl

theorem ch89401_cnt : cntK = true := by quickRfl

end CertificateChecks.KernelAS91K42
