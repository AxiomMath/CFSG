module

public import Certificates.Data.Kernel.OpsK
public import Certificates.Data.Kernel.MonsterB.FischerBT
public import CFSG.RankThree.Asc83Table.MatCertDefs

public section

namespace CFSG.KC.OpsMB

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.KC.OpsK CFSG.KC.FischerB

variable {V : Type} (O : Ops Nat V)

@[expose] noncomputable def stepB (T : BT) (k : BT → Bool) (op : Op) : Bool :=
  Op.rec (motive := fun _ => Bool)
    (fun i j t => forceB (O.mul (getT T i) (getT T j)) fun a => k (setT T t a))
    (fun e i t => forceB (powN O (Nat.succ e) (getT T i) e) fun a => k (setT T t a)) op

@[expose] noncomputable def runB (prog : List Op) : BT → (BT → Bool) → Bool :=
  List.rec (motive := fun _ => BT → (BT → Bool) → Bool)
    (fun T k => k T) (fun op _ ih T k => stepB O T (fun T' => ih T' k) op) prog

@[expose] noncomputable def evalWB (T : BT) : Word → Nat
  | [] => O.one
  | (r, e) :: w => O.mul (powN O (Nat.succ e) (getT T r) e) (evalWB T w)

@[expose] noncomputable def factB (T : BT) (n : Nat) : MFact → Bool
  | .ord r e => decide (r < n) && decide (0 < e) &&
      O.eq (powN O (Nat.succ e) (getT T r) e) O.one
  | .conj h u w => decide (h < n) && wordLt n u && wordLt n w &&
      O.eq (O.mul (getT T h) (evalWB O T u)) (O.mul (evalWB O T w) (getT T h))
  | .ne w₁ w₂ t => wordLt n w₁ && wordLt n w₂ &&
      O.vne (O.vmul (O.unit t) (evalWB O T w₁)) (O.vmul (O.unit t) (evalWB O T w₂))
  | .eq w₁ w₂ => wordLt n w₁ && wordLt n w₂ && O.eq (evalWB O T w₁) (evalWB O T w₂)

@[expose] noncomputable def initB (A B : Nat) : BT :=
  setT (setT (mkB O.one 11) 0 A) 1 B

@[expose] noncomputable def seedRunB (A B : Nat) (C : MCert) : Bool :=
  runB O C.prog (initB O A B) fun T =>
    decide (2 ≤ C.nregs) && decide (C.nregs ≤ 2048) && C.prog.all (Op.lt C.nregs) &&
      C.facts.all (factB O T C.nregs) && O.eq (getT T 0) A && O.eq (getT T 1) B

end CFSG.KC.OpsMB

end
