module

public import Certificates.Kernel.AutJ2Vtx.KTbl
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAJV

open CFSG.Quasithin.F112R.St84.AutJ2Model CFSG.Quasithin.F112R.St84.Heis
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim

@[expose] noncomputable def ppK (p e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn 315 9) (fun _ acc => pcomp 315 9 (mask 9) p acc) e

@[expose] noncomputable def pE (P1 P2 a : Nat) : Nat :=
  pcomp 315 9 (mask 9) (ppK P1 (a % 2)) (ppK P2 (a / 2))

@[expose] noncomputable def pEI (I1 I2 b : Nat) : Nat :=
  pcomp 315 9 (mask 9) (ppK I2 (b / 2)) (ppK I1 (b % 2))

@[expose] noncomputable def κG (E1 E2 F1 F2 E1I F1I F2I a b w : Nat) : Nat :=
  pcomp 315 9 (mask 9) (pcomp 315 9 (mask 9) (pE E1 E2 a) (pE F1 F2 b))
    (pcomp 315 9 (mask 9) (pcomp 315 9 (mask 9) (pcomp 315 9 (mask 9) E1 (pE F1 F2 w)) E1I)
      (pEI F1I F2I w))

@[expose] noncomputable def κQ (q : Q1M) : Nat :=
  κG (AJT 14) (AJT 15) (AJT 16) (AJT 17) (AJI 14) (AJI 16) (AJI 17) q.a.code.val q.b.code.val
    (q.c + q.a * q.b).code.val

theorem kK : allN 64 (fun i => Nat.beq (AJK i) (κQ (q1mOfCode i))) = true := by quickRfl

@[expose] noncomputable def homRow (i : Nat) : Bool :=
  allN 64 fun j => Nat.beq (AJK (q1mIdx (q1mOfCode i * q1mOfCode j)).val)
    (pcomp 315 9 (mask 9) (AJK i) (AJK j))

theorem kHom0 : allN 16 (fun i => homRow i) = true := by quickRfl

theorem kHom1 : allN 16 (fun i => homRow (Nat.add i 16)) = true := by quickRfl

theorem kHom2 : allN 16 (fun i => homRow (Nat.add i 32)) = true := by quickRfl

theorem kHom3 : allN 16 (fun i => homRow (Nat.add i 48)) = true := by quickRfl

theorem kInj : allN 64 (fun i => Nat.beq i 0 || !Nat.beq (AJK i) (pidn 315 9)) = true := by
  quickRfl

@[expose] noncomputable def cgK (c : Nat) (α : MulAut Q1M) : Bool :=
  [e1, e2, f1, f2].all fun g =>
    Nat.beq (pcomp 315 9 (mask 9) (pcomp 315 9 (mask 9) (AJT c) (AJK (q1mIdx g).val)) (AJI c))
      (AJK (q1mIdx (α g)).val)

theorem kC5 : (cgK 21 ρM && cgK 20 βM && cgK 18 τM && cgK 19 γM) = true := by quickRfl

end CertificateChecks.KernelAJV

end
