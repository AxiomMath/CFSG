module

public import Certificates.Data.Kernel.AS91K468.K48
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelAS91K468

open Certificates.Kernel.AS91K468 Certificates.Kernel.HJ12K CFSG.KC.Mat12P

theorem ch89408_crd : CFSG.Quasithin.H13.AS91.Two.crdOK48 () = true := by quickRfl

theorem ch89408_s48 : s48OK = true := by quickRfl

theorem ch89408_pbar : pbarOK = true := by quickRfl

theorem ch89408_b7 : b7OK = true := by quickRfl

theorem ch89408_r64 : r64OK = true := by quickRfl

theorem ch89408_stab : stab48Q = true := by quickRfl

theorem ch89408_c3 : c348Q = true := by quickRfl

theorem ch89408_i : i48Q = true := by quickRfl

theorem ch89408_tb : tBase48Q = true := by quickRfl

theorem ch89408_tn0 : tNorm48Q 0 = true := by quickRfl

theorem ch89408_tn1 : tNorm48Q 1 = true := by quickRfl

theorem ch89408_tn2 : tNorm48Q 2 = true := by quickRfl

theorem ch89408_tn3 : tNorm48Q 3 = true := by quickRfl

theorem ch89408_tn4 : tNorm48Q 4 = true := by quickRfl

theorem ch89408_tn5 : tNorm48Q 5 = true := by quickRfl

theorem ch89408_tn6 : tNorm48Q 6 = true := by quickRfl

theorem ch89408_tn7 : tNorm48Q 7 = true := by quickRfl

theorem ch89408_tn8 : tNorm48Q 8 = true := by quickRfl

theorem ch89408_tn9 : tNorm48Q 9 = true := by quickRfl

theorem ch89408_tn10 : tNorm48Q 10 = true := by quickRfl

theorem ch89408_tn11 : tNorm48Q 11 = true := by quickRfl

theorem ch89408_tn12 : tNorm48Q 12 = true := by quickRfl

theorem ch89408_tn13 : tNorm48Q 13 = true := by quickRfl

theorem ch89408_tn14 : tNorm48Q 14 = true := by quickRfl

theorem ch89408_tn15 : tNorm48Q 15 = true := by quickRfl

theorem ch89408_tc : tCent48Q = true := by quickRfl

theorem ch89408_fus : fus48Q = true := by quickRfl

theorem ch89408_orb : orb48Q = true := by quickRfl

end CertificateChecks.KernelAS91K468
