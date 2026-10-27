module

public import Certificates.Kernel.Co1SevenK.BndData
public import Certificates.Kernel.Co1SevenK.Syl
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Data.Kernel.Co1BBoundP
public import Certificates.Data.Kernel.Co1BW
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1SevenK

open CFSG.KC.Co1BBoundP CFSG.KC.Co1BBoundN CFSG.KC.Co1BBound CFSG.KC.Co1BSpin CFSG.KC.Co1B
  CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT
open CertificateChecks.KernelCo1B.Bound17591 (XB)

theorem kBTA : (Nat.beq BD.TA.length 7 &&
    allN 7 fun s => eqK (getL 0 BD.TA s) (trK 24 (powWK SK s))) = true := by quickRfl

theorem kBTB : (Nat.beq BD.TB.length 7 &&
    allN 7 fun s => eqK (getL 0 BD.TB s) (trK 24 (powWK TK s))) = true := by quickRfl

theorem kCFA : decide (BD.CFA = (List.range 4).map fun i =>
    storeSel 7 XB BD.TA (BD.baseA.take i) (BD.baseA.getD i 0) (BD.condsA.getD i [])
      (BD.SelA.getD i [])) = true := by
  quickRfl

theorem kCFB : decide (BD.CFB = (List.range 6).map fun i =>
    storeSel 7 XB BD.TB (BD.baseB.take i) (BD.baseB.getD i 0) (BD.condsB.getD i [])
      (BD.SelB.getD i [])) = true := by
  quickRfl

theorem kNA : (Nat.beq BD.baseA.length 4 && Nat.beq BD.condsA.length 4 &&
    Nat.beq BD.cntsA.length 4 && Nat.beq BD.CNA.length 4 && Nat.beq BD.cntsA.prod 17640 &&
    allN 4 fun i => memK XB (BD.baseA.getD i 0) &&
      Nat.beq (BD.CNA.getD i []).length 9 &&
      Nat.ble (BD.CNA.getD i []).sum (BD.cntsA.getD i 0)) = true := by
  quickRfl

theorem kNB : (Nat.beq BD.baseB.length 6 && Nat.beq BD.condsB.length 6 &&
    Nat.beq BD.cntsB.length 6 && Nat.beq BD.CNB.length 6 && Nat.beq BD.cntsB.prod 1176 &&
    allN 6 fun i => memK XB (BD.baseB.getD i 0) &&
      Nat.beq (BD.CNB.getD i []).length 9 &&
      Nat.ble (BD.CNB.getD i []).sum (BD.cntsB.getD i 0)) = true := by
  quickRfl

theorem kSpanA : (Nat.beq BD.spanA.length 24 && Nat.beq BD.combA.length 24 &&
    BD.spanA.all (fun s => Nat.blt s.1 4 && Nat.blt s.2 7) &&
    allN 24 (fun l => Nat.beq (vmF 24 (packL (BD.spanA.map (slotKn 7 BD.TA BD.baseA)))
      (BD.combA.getD l 0)) (Nat.shiftLeft 1 l))) = true := by quickRfl

theorem kSpanB : (Nat.beq BD.spanB.length 24 && Nat.beq BD.combB.length 24 &&
    BD.spanB.all (fun s => Nat.blt s.1 6 && Nat.blt s.2 7) &&
    allN 24 (fun l => Nat.beq (vmF 24 (packL (BD.spanB.map (slotKn 7 BD.TB BD.baseB)))
      (BD.combB.getD l 0)) (Nat.shiftLeft 1 l))) = true := by quickRfl

end CertificateChecks.KernelCo1SevenK

end
