module

public import Certificates.Kernel.CU43Aut.Small
public import Certificates.Kernel.CU43Aut.SylData
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Data3
meta import Certificates.Kernel.CU43Aut.SylData
meta import Certificates.Data.CFSGNative.PSL3Four.Basic
meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelCU43Aut.SylM

open CFSG.PSL3Four.Native

meta def idM : Array Nat := idTab 820

meta def idsM : Array (Array Nat) := Array.replicate 7 idM

meta def tgM : Array (Array Nat) := CertificateChecks.KernelCU43Aut.SylJ.tg

meta def recM : Array (Array Nat) :=
  (bfs (fun j t => conjTab 820 idsM[j]! tgM[j]! t) 7 idM 1024).tabs

meta def ivM : Array (Array Nat) :=
  (recM.filter fun t => comp 820 t t == idM && t != idM).qsort fun a b =>
    CFSG.KS.RawGen.pack 10 a < CFSG.KS.RawGen.pack 10 b

end CertificateChecks.KernelCU43Aut.SylM

#kmulh CertificateChecks.KernelCU43Aut.TS 820 10 CertificateChecks.KernelCU43Aut.SylM.idsM
  CertificateChecks.KernelCU43Aut.SylM.tgM CertificateChecks.KernelCU43Aut.SylM.idM 1024

#kfind CertificateChecks.KernelCU43Aut.TS.IV CertificateChecks.KernelCU43Aut.SylM.recM
  CertificateChecks.KernelCU43Aut.SylM.ivM

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCU43Aut

open CFSG.EvenSporadicStandard.M24Std.CU43
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CertificateChecks.KernelU43B

@[expose] noncomputable def involT (i : Nat) : Bool :=
  bAnd(Nat.beq (pc (TS.T i) (TS.T i)) (pidn 820 10),
    bIf(Nat.beq (TS.T i) (pidn 820 10), false, true))

@[expose] noncomputable def nInvT (c : Nat) : Nat :=
  foldUp c (fun i acc => nIf(involT i, Nat.succ acc, acc)) (nat_lit 0)

@[expose] noncomputable def ivW (q : Nat) : Bool :=
  strictB (r32 TS.IV q) (fun i => strictB (WJ q) (fun j =>
    bAnd(Nat.blt i TS.cnt, bAnd(involT i, bAnd(Nat.blt j (nat_lit 9), bAnd(inPK (WP q),
      Nat.beq (pc (WP q) (CU43T (Nat.add j (nat_lit 2)))) (pc (TS.T i) (WP q))))))))

theorem tBase : bAnd(szOK 820 10, bAnd(cK (pidn 820 10), bAnd(CFSG.KS.Prim.idK 820 10 (mask 10),
    bAnd(allN 7 (fun j => bAnd(cK (TS.GI j), Nat.beq (TS.G j) (pidn 820 10))),
    bAnd(Nat.beq TS.cnt 1024, penumHdK (pidn 820 10) TS.cnt 1024 TS.T TS.PL))))) = true := by
  quickRfl

theorem tBind : bindListK 820 10 (TS.GI 0) sylGen0.toList = true ∧
    bindListK 820 10 (TS.GI 1) sylGen1.toList = true ∧
    bindListK 820 10 (TS.GI 2) sylGen2.toList = true ∧
    bindListK 820 10 (TS.GI 3) sylGen3.toList = true ∧
    bindListK 820 10 (TS.GI 4) sylGen4.toList = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> quickRfl

theorem tIn : bAnd(allN 5 (fun j => inPK (TS.GI j)), bAnd(inPK (pc (TS.GI 5) (CU43TI 0)),
    inPK (pc (TS.GI 6) (CU43TI 1)))) = true := by
  quickRfl

@[expose] noncomputable def slT (s : Nat) : Bool :=
  penumSlK 820 10 (mask 10) (820 * 10) true TS.G TS.GI 7 TS.cnt TS.T TS.PL TS.POS TS.SRT TS.SRI
    (Nat.mul 128 s) 128

theorem tE0 : slT 0 = true := by quickRfl
theorem tE1 : slT 1 = true := by quickRfl
theorem tE2 : slT 2 = true := by quickRfl
theorem tE3 : slT 3 = true := by quickRfl
theorem tE4 : slT 4 = true := by quickRfl
theorem tE5 : slT 5 = true := by quickRfl
theorem tE6 : slT 6 = true := by quickRfl
theorem tE7 : slT 7 = true := by quickRfl

theorem tH : slK TS.cnt (hsortPtK 820 10 (mask 10) TS.cnt TS.T TS.HS TS.HSI) 0 TS.cnt = true := by
  quickRfl

theorem tIvN : Nat.beq (nInvT 1024) 191 = true := by quickRfl

theorem tIvS : allN 190 (fun q => Nat.blt (TS.T (r32 TS.IV q)) (TS.T (r32 TS.IV (Nat.succ q)))) =
    true := by
  quickRfl

theorem tW0 : allN 96 ivW = true := by quickRfl

theorem tW1 : allN 95 (fun q => ivW (Nat.add 96 q)) = true := by quickRfl

end CertificateChecks.KernelCU43Aut

end
