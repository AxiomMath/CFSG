module

public import Certificates.Kernel.CU43Aut.Tabs
public import Certificates.Kernel.Multipliers.U43BChain
public import CFSG.Certificates.Kernel.Spor.BindList
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCU43Aut

open CFSG.EvenSporadicStandard.M24Std.CU43
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CertificateChecks.KernelU43B

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 820 10 (mask 10) (820 * 10) p

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 820 10 (mask 10) p q

@[expose] noncomputable def ppow (p : Nat) (e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn 820 10) (fun _ acc => pc p acc) e

@[expose] noncomputable def TK (k : Nat) : Nat :=
  pc (ppow (CU43T 1) (Nat.div k 4)) (ppow (CU43T 0) (Nat.mod k 4))

@[expose] noncomputable def TKI (k : Nat) : Nat := pinvS 820 10 (mask 10) (TK k)

@[expose] noncomputable def inPK (p : Nat) : Bool :=
  siftK 820 10 (mask 10) (820 * 10) (pidn 820 10) C.LR C.TRI C.BP 3 0 p

theorem kBind : bindListK 820 10 (CU43T 0) deltaArr.toList = true ∧
    bindListK 820 10 (CU43T 1) phiArr.toList = true ∧
    bindListK 820 10 (CU43T 2) rep0.toList = true ∧
    bindListK 820 10 (CU43T 3) rep1.toList = true ∧
    bindListK 820 10 (CU43T 4) rep2.toList = true ∧
    bindListK 820 10 (CU43T 5) rep3.toList = true ∧
    bindListK 820 10 (CU43T 6) rep4.toList = true ∧
    bindListK 820 10 (CU43T 7) rep5.toList = true ∧
    bindListK 820 10 (CU43T 8) rep6.toList = true ∧
    bindListK 820 10 (CU43T 9) rep7.toList = true ∧
    bindListK 820 10 (CU43T 10) rep8.toList = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> quickRfl

theorem kSz : (szOK 820 10 && cK (pidn 820 10) && CFSG.KS.Prim.idK 820 10 (mask 10)) = true := by
  quickRfl

theorem kIn : allN 11 (fun i => bAnd(cK (CU43T i), bAnd(cK (CU43TI i),
    invEqK 820 10 (mask 10) (820 * 10) (CU43T i) (CU43TI i)))) = true := by
  quickRfl

theorem kTK : allN 8 (fun k => bAnd(cK (TK k), permOK 820 10 (mask 10) (820 * 10) (TK k) (TKI k))) =
    true := by
  quickRfl

theorem kNorm : allN 2 (fun u => allN 2 (fun g =>
    inPK (pc (pc (CU43T u) (C.S g)) (CU43TI u)))) = true := by
  quickRfl

theorem kRel : (Nat.beq (ppow (CU43T 0) 4) (pidn 820 10) && Nat.beq (ppow (CU43T 1) 2) (pidn 820 10) &&
    Nat.beq (pc (CU43T 1) (pc (CU43T 0) (CU43T 1))) (ppow (CU43T 0) 3)) = true := by
  quickRfl

theorem kCos : allN 7 (fun m => !inPK (TK (Nat.succ m))) = true := by
  quickRfl

theorem kRep : allN 9 (fun j => bAnd(Nat.beq (pc (CU43T (Nat.add j 2)) (CU43T (Nat.add j 2)))
    (pidn 820 10), inPK (pc (CU43T (Nat.add j 2)) (TKI (repCoset.getD j 0))))) = true := by
  quickRfl

end CertificateChecks.KernelCU43Aut

end
