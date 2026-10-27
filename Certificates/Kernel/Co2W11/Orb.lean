module

public import Certificates.Data.Kernel.F2PtSet
public import Certificates.Data.Kernel.F2FormId
public import Certificates.Data.Kernel.F2OrbW
public import Certificates.Kernel.Co2W11.OrbData
public import Certificates.Kernel.Co2W11.FormsData
public import Certificates.Kernel.Co2W11.Sep
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCo2W11

open CFSG.KC.F2PtSet CFSG.KC.F2TriSep CFSG.KC.F2FormId CFSG.KC.F2OrbW CFSG.KC.M1F2 CFSG.KC.Co1F2
  CFSG.KLie.CT CFSG.KC.F2W CertificateChecks.KernelLC.Co2Ops

theorem o0_ok : (sortK 22 2300 Ob.P0 && forK 22 2300 Ob.P0 Ob.E0 [trK 22 SA.M, trK 22 SB.M] [40] &&
    imgK 22 2300 Ob.P0 (trK 22 SA.M) Ob.TA && imgK 22 2300 Ob.P0 (trK 22 SB.M) Ob.TB) = true := by
  quickRfl

theorem scan_ok : (gapsK 22 2300 Ob.P0 2300 Ob.P0 Ob.W1 (Nat.xor 65536) &&
    Nat.beq (cntK 22 2300 Ob.P0 Ob.P0 Ob.W1 (Nat.xor 65536) (fun _ => true) true) 44 &&
    gapsK 22 2300 Ob.P0 2300 Ob.P0 Ob.W2 (Nat.xor 8) &&
    Nat.beq (cntK 22 2300 Ob.P0 Ob.P0 Ob.W2 (Nat.xor 8) (fun _ => true) true) Ob.b2 &&
    gapsK 22 2300 Ob.P0 2300 Ob.P0 Ob.W3 (Nat.xor (Nat.xor 8 Ob.urep)) &&
    Nat.beq (cntK 22 2300 Ob.P0 Ob.P0 Ob.W3 (Nat.xor (Nat.xor 8 Ob.urep)) (fun _ => true) true)
      Ob.b3 &&
    gapK 22 2300 Ob.P0 65536 Ob.g1 && notB (inW 22 Ob.P0 65536 Ob.g1) &&
    gapK 22 2300 Ob.P0 8 Ob.g2 && notB (inW 22 Ob.P0 8 Ob.g2)) = true := by
  quickRfl

theorem z1_ok : (sortK 22 891 Ob.PZ1 &&
    forK 22 891 Ob.PZ1 Ob.EZ1 (trL 22 (gensOf S0.words)) [Nat.xor 40 Ob.u0]) = true := by
  quickRfl

theorem d2_ok : (sortK 22 1120 Ob.PD2 &&
    forK 22 1120 Ob.PD2 Ob.ED2 (trL 22 (gensOf S2.words)) [Ob.urep] &&
    gapsK 22 2300 Ob.P0 1120 Ob.PD2 Ob.WL (fun x => x) &&
    Nat.beq (cntK 22 2300 Ob.P0 Ob.PD2 Ob.WL (fun x => x) (fun x => notB (dotK 22 x Ob.lam2))
      false) 28) = true := by
  quickRfl

theorem z_ok : (sortK 22 1232 Ob.PZ &&
    forK 22 1232 Ob.PZ Ob.EZ (trL 22 (gensOf S1.words)) (Ob.ws2.map Prod.fst)) = true := by
  quickRfl

theorem words_ok :
    (wordsToK 22 SA.M SB.M 8 Ob.ws2 && wordsToK 22 SA.M SB.M 65536 Ob.ws1) = true := by
  quickRfl

theorem rel_ok : (Nat.blt Ob.iu0 2300 && Nat.beq (fget Ob.P0 Ob.iu0 22) Ob.u0 &&
    Nat.blt Ob.iurep 2300 && Nat.beq (fget Ob.P0 Ob.iurep 22) Ob.urep &&
    eqL (Ob.ws1.map Prod.fst) [Nat.xor 40 Ob.u0] &&
    eqL ((Ob.ws2.map Prod.fst).map (Nat.xor 65536)) (Ob.izs.map fun k => fget Ob.P0 k 22) &&
    Ob.izs.all (fun k => Nat.blt k 2300) &&
    notB (Nat.beq Ob.b2 44) && notB (Nat.beq Ob.b3 44) && Nat.beq Ob.nZ 1232) = true := by
  quickRfl

theorem span_ok : (Nat.beq (lenL Ob.bidx) 22 && Ob.bidx.all (fun k => Nat.blt k 2300) &&
    Nat.beq (mulW 22 (packL 22 (ptsL 22 Ob.P0 Ob.bidx)) Ob.Bi) (idF 22)) = true := by
  quickRfl

theorem hyp_ok : (Nat.beq (mulW 22 Ob.Pm Ob.Pmi) (idF 22) &&
    altK 22 (Nat.xor (mulW 22 (mulW 22 (trK 22 Ob.Pm) Fm.Q) Ob.Pm) (hypF 11))) = true := by
  quickRfl

end CertificateChecks.KernelCo2W11

end
