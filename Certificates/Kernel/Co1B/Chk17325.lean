module

public import Certificates.Kernel.Co1B.Data17325
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Kernel.Co1ThreeK.Letters
public import Certificates.Data.Kernel.Co1BW
public import Certificates.Data.Kernel.Co1BBoundN
public import Certificates.Data.Kernel.Co1BBoundP
public import Certificates.Data.Kernel.SporSch.Co1Bfs
public import Certificates.Data.TabCo1FiveB
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17325

open CFSG.KC.Co1BBoundP CFSG.KC.Co1BBoundN CFSG.KC.Co1BBound CFSG.KC.Co1BSpin CFSG.KC.Co1B
  CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KS.SporSch.M24
  CFSG.HardMathSupport.Dickson.I271.TabCo1FiveB
open CertificateChecks.KernelCo1B.Bound17591 (XB)

@[expose] noncomputable def KK : Nat := DB.M 87
@[expose] noncomputable def X1K : Nat := DB.M 88
@[expose] noncomputable def Y1K : Nat := DB.M 89
@[expose] noncomputable def TK : Nat := DB.M 90
@[expose] noncomputable def TI : Nat := DB.MI 90
@[expose] noncomputable def X2K : Nat := mulWK (mulWK TK X1K) TI
@[expose] noncomputable def Y2K : Nat := mulWK (mulWK TK Y1K) TI
@[expose] noncomputable def LM (l : Nat) : Nat := DB.M (Nat.add 88 l)
@[expose] noncomputable def LI (i : Nat) : Nat := getL 0 KB.LI i
@[expose] noncomputable def PTB : List Nat := [KK, X1K, Y1K, X2K, Y2K]

theorem kDB : dagWK DB.M DB.MI 2 91 KB.KW = true := by quickRfl

theorem kDBB : (Nat.beq (DB.M 0) (CertificateChecks.KernelCo1ThreeK.L.M 9) &&
    Nat.beq (DB.M 1) (CertificateChecks.KernelCo1ThreeK.L.M 10)) = true := by quickRfl

theorem kDBW : KB.KW.map CFSG.Sporadic.Co1Schreier.Native.decWord =
    CFSG.HardMathSupport.Dickson.I271.TabCo1.chainDerivs () ++ ext := by decide +kernel

theorem kSmall : (eqK KK KB.D1 && eqK (powWK KK 5) oneK && notB (eqK KK oneK) &&
    eqK (mulWK KK X1K) (mulWK X1K KK) && eqK (mulWK KK Y1K) (mulWK Y1K KK) &&
    eqK (mulWK KK TK) (mulWK TK KK) && eqK (mulWK TK TK) oneK &&
    eqK (mulWK X1K X2K) (mulWK X2K X1K) && eqK (mulWK X1K Y2K) (mulWK Y2K X1K) &&
    eqK (mulWK Y1K X2K) (mulWK X2K Y1K) && eqK (mulWK Y1K Y2K) (mulWK Y2K Y1K)) = true := by
  quickRfl

theorem kLT : (gtPinK LM 2 200 LT.N LT.P LT.PAR LT.LAB LT.W LT.S && Nat.beq LT.N 60) = true := by
  quickRfl

theorem kInv : allN 60 (fun i => invOKW (LT.P i) (LI i)) = true := by quickRfl

theorem kCW : (Nat.blt (getL 0 KB.CW 0) 60 && Nat.blt (getL 0 KB.CW 1) 60 &&
    Nat.blt (getL 0 KB.CW 2) 60 && Nat.blt (getL 0 KB.CW 3) 60 &&
    eqK (mulWK (mulWK (LT.P (getL 0 KB.CW 0)) (LT.P (getL 0 KB.CW 1)))
      (mulWK (LI (getL 0 KB.CW 0)) (LI (getL 0 KB.CW 1)))) X1K &&
    eqK (mulWK (mulWK (LT.P (getL 0 KB.CW 2)) (LT.P (getL 0 KB.CW 3)))
      (mulWK (LI (getL 0 KB.CW 2)) (LI (getL 0 KB.CW 3)))) Y1K) = true := by quickRfl

theorem kT : (Nat.beq KB.T.length 5 &&
    allN 5 fun i => eqK (getL 0 KB.T i) (trK 24 (powWK KK i))) = true := by quickRfl

theorem kT2 : (Nat.beq KB.T2.length 5 &&
    allN 5 fun i => eqK (getL 0 KB.T2 i) (trK 24 (getL 0 PTB i))) = true := by quickRfl

theorem kSpan : (Nat.beq span.length 24 && Nat.beq comb.length 24 &&
    span.all (fun s => Nat.blt s.1 8 && Nat.blt s.2 5) &&
    allN 24 (fun l => Nat.beq (vmF 24 (packL (span.map (slotKn 5 KB.T base))) (comb.getD l 0))
      (Nat.shiftLeft 1 l))) = true := by quickRfl

theorem kSpan2 : (Nat.beq span2.length 24 && Nat.beq comb2.length 24 &&
    span2.all (fun s => Nat.blt s.1 6 && Nat.blt s.2 5) &&
    allN 24 (fun l => Nat.beq (vmF 24 (packL (span2.map (slotKn 5 KB.T2 base2))) (comb2.getD l 0))
      (Nat.shiftLeft 1 l))) = true := by quickRfl

theorem kCFs : decide (KB.CFs = (List.range 8).map fun i =>
    storeSel 5 XB KB.T (base.take i) (base.getD i 0) (conds.getD i []) (KB.Sel.getD i [])) = true := by
  quickRfl

theorem kCFs2 : decide (KB.CFs2 = (List.range 6).map fun i =>
    storeSel 5 XB KB.T2 (base2.take i) (base2.getD i 0) (conds2.getD i []) (KB.Sel2.getD i [])) =
    true := by
  quickRfl

theorem kNs : (Nat.beq KB.CNs.length 8 && allN 8 fun i => memK XB (base.getD i 0) &&
    Nat.beq (KB.CNs.getD i []).length 9 && Nat.ble (KB.CNs.getD i []).sum (cnts.getD i 0)) = true := by
  quickRfl

theorem kNs2 : (Nat.beq KB.CNs2.length 6 && allN 6 fun i => memK XB (base2.getD i 0) &&
    Nat.beq (KB.CNs2.getD i []).length 9 && Nat.ble (KB.CNs2.getD i []).sum (cnts2.getD i 0)) =
    true := by
  quickRfl

end CertificateChecks.KernelCo1B.Bound17325

end
