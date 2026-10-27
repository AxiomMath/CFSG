module

public import Certificates.Kernel.Co1B.Data17326
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Kernel.Co1ThreeK.Letters
public import Certificates.Data.Kernel.Co1BW
public import Certificates.Data.Kernel.Co1BBoundN
public import Certificates.Data.Kernel.Co1BBoundP
public import Certificates.Data.Kernel.SporSch.Co1Bfs
public import Certificates.Data.TabCo1FiveC
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17326

open CFSG.KC.Co1BBoundP CFSG.KC.Co1BBoundN CFSG.KC.Co1BBound CFSG.KC.Co1BSpin CFSG.KC.Co1B
  CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KS.SporSch.M24
  CFSG.HardMathSupport.Dickson.I271.TabCo1FiveC
open CertificateChecks.KernelCo1B.Bound17591 (XB)

@[expose] noncomputable def ZK : Nat := DC.M 87
@[expose] noncomputable def T1K : Nat := DC.M 88
@[expose] noncomputable def T2K : Nat := DC.M 89
@[expose] noncomputable def S1K : Nat := DC.M 90
@[expose] noncomputable def S2K : Nat := DC.M 91
@[expose] noncomputable def TM (l : Nat) : Nat := DC.M (Nat.add 88 l)
@[expose] noncomputable def PT2 : List Nat :=
  [ZK, T1K, T2K, mulWK T1K T2K, mulWK T1K (powWK T2K 2), mulWK (powWK T1K 2) T2K,
    mulWK (powWK T1K 2) (powWK T2K 2)]

theorem kDC : dagWK DC.M DC.MI 2 92 KC.KW = true := by quickRfl

theorem kDCB : (Nat.beq (DC.M 0) (CertificateChecks.KernelCo1ThreeK.L.M 9) &&
    Nat.beq (DC.M 1) (CertificateChecks.KernelCo1ThreeK.L.M 10)) = true := by quickRfl

theorem kDCW : KC.KW.map CFSG.Sporadic.Co1Schreier.Native.decWord =
    CFSG.HardMathSupport.Dickson.I271.TabCo1.chainDerivs () ++ ext := by decide +kernel

theorem kSmall : (eqK (powWK ZK 5) oneK && notB (eqK ZK oneK) && eqK ZK KC.Z0 &&
    eqK (mulWK ZK T1K) (mulWK T1K ZK) && eqK (mulWK ZK T2K) (mulWK T2K ZK) &&
    eqK (mulWK ZK S1K) (mulWK S1K ZK) && eqK (mulWK ZK S2K) (mulWK S2K ZK) &&
    eqK ZK (mulWK (mulWK T1K T2K) (mulWK (DC.MI 88) (DC.MI 89)))) = true := by quickRfl

theorem kTT : (gtPinK TM 2 200 TT.N TT.P TT.PAR TT.LAB TT.W TT.S && Nat.beq TT.N 125) = true := by
  quickRfl

theorem kNorm : (bfsMemK TT.P TT.S TT.N (mulWK (mulWK S1K T1K) (DC.MI 90)) &&
    bfsMemK TT.P TT.S TT.N (mulWK (mulWK S1K T2K) (DC.MI 90)) &&
    bfsMemK TT.P TT.S TT.N (mulWK (mulWK S2K T1K) (DC.MI 91)) &&
    bfsMemK TT.P TT.S TT.N (mulWK (mulWK S2K T2K) (DC.MI 91)) &&
    bfsMemK TT.P TT.S TT.N (mulWK (mulWK (DC.MI 90) T1K) S1K) &&
    bfsMemK TT.P TT.S TT.N (mulWK (mulWK (DC.MI 90) T2K) S1K) &&
    bfsMemK TT.P TT.S TT.N (mulWK (mulWK (DC.MI 91) T1K) S2K) &&
    bfsMemK TT.P TT.S TT.N (mulWK (mulWK (DC.MI 91) T2K) S2K)) = true := by quickRfl

theorem kT : (Nat.beq KC.T.length 5 &&
    allN 5 fun i => eqK (getL 0 KC.T i) (trK 24 (powWK ZK i))) = true := by quickRfl

theorem kT2 : (Nat.beq KC.T2.length 7 &&
    allN 7 fun i => eqK (getL 0 KC.T2 i) (trK 24 (getL 0 PT2 i))) = true := by quickRfl

theorem kSpan : (Nat.beq span.length 24 && Nat.beq comb.length 24 &&
    span.all (fun s => Nat.blt s.1 7 && Nat.blt s.2 5) &&
    allN 24 (fun l => Nat.beq (vmF 24 (packL (span.map (slotKn 5 KC.T base))) (comb.getD l 0))
      (Nat.shiftLeft 1 l))) = true := by quickRfl

theorem kSpan2 : (Nat.beq span2.length 24 && Nat.beq comb2.length 24 &&
    span2.all (fun s => Nat.blt s.1 4 && Nat.blt s.2 7) &&
    allN 24 (fun l => Nat.beq (vmF 24 (packL (span2.map (slotKn 7 KC.T2 base2))) (comb2.getD l 0))
      (Nat.shiftLeft 1 l))) = true := by quickRfl

theorem kCFs : decide (KC.CFs = (List.range 7).map fun i =>
    storeSel 5 XB KC.T (base.take i) (base.getD i 0) (conds.getD i []) (KC.Sel.getD i [])) = true := by
  quickRfl

theorem kCFs2 : decide (KC.CFs2 = (List.range 4).map fun i =>
    storeSel 7 XB KC.T2 (base2.take i) (base2.getD i 0) (conds2.getD i []) (KC.Sel2.getD i [])) =
    true := by
  quickRfl

theorem kNs : (Nat.beq KC.CNs.length 7 && allN 7 fun i => memK XB (base.getD i 0) &&
    Nat.beq (KC.CNs.getD i []).length 9 && Nat.ble (KC.CNs.getD i []).sum (cnts.getD i 0)) = true := by
  quickRfl

theorem kNs2 : (Nat.beq KC.CNs2.length 4 && allN 4 fun i => memK XB (base2.getD i 0) &&
    Nat.beq (KC.CNs2.getD i []).length 9 && Nat.ble (KC.CNs2.getD i []).sum (cnts2.getD i 0)) =
    true := by
  quickRfl

end CertificateChecks.KernelCo1B.Bound17326

end
