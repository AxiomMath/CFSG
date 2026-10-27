module

public import Certificates.Data.Kernel.Co2Span.Check
public import Certificates.Kernel.Co2Span.Data
public import Certificates.Data.GF2W1112Co2U

public section

namespace CertificateChecks.KernelCo2Span

open CFSG.KC.Co2Span CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.GF2W1112

theorem ch38960yz : allN (fun k =>
    xPackS 9 (sgOf w12UDecSigma (2 + k)) (cbOf w12UDecU (2 + k)) == D.YP.getD k 0 &&
      xPackS 9 (sgOf w12UDecSigma (5 + k)) (cbOf w12UDecU (5 + k)) == D.ZP.getD k 0) 3 = true := by
  decide +kernel

theorem ch38960rows : allN (fun i => rowsAgree (w12UBRows[i]!) (D.BP.getD i 0)) 11 &&
    rowsAgree w12UM0Rows D.M0P = true := by
  decide +kernel

theorem ch38960sol : allN (fun i => allN (fun k =>
    eqK (mulV (D.BP.getD i 0) (D.YP.getD k 0)) (mulV (D.ZP.getD k 0) (D.BP.getD i 0))) 3) 11 =
      true := by
  decide +kernel

theorem ch38960free : allN (fun i => allN (fun j =>
    (D.BP.getD i 0).testBit (w12UFree.getD j 0) == (i == j)) 11) 11 = true := by
  decide +kernel

theorem ch38960peel : peelK D.YP D.ZP (maskOf w12UFree) D.STEPS = true := by
  decide +kernel

theorem ch38961x : allN (fun c =>
    xPackS c (sgOf w12UDecSigma 0) (cbOf w12UDecU 0) == D.XC0.getD c 0 &&
      xPackS c (sgOf w12UDecSigma 1) (cbOf w12UDecU 1) == D.XC1.getD c 0) 16 = true := by
  decide +kernel

theorem ch38961q : allN (fun i => xPackS (w12USCodes.getD i 0) sgId cbId == D.QP.getD i 0) 6 =
    true := by
  decide +kernel

theorem ch38961enum : enumP D.BP D.XC0 D.XC1 w12UTauWords.toList w12UTauOrd.toList D.QP
    (D.XC0.getD 9 0) (D.XC1.getD 11 0) D.M0P = true := by
  decide +kernel

end CertificateChecks.KernelCo2Span
