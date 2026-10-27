module

public import Certificates.Data.Kernel.OpsK
public import CFSG.RankThree.Asc83Table.MatCertDefs

public section

namespace CFSG.KC.OpsMN

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.KC.OpsK

variable {V : Type} (O : Ops Nat V)

@[expose] def getN (R : List Nat) (r : Nat) : Nat := R.getD r 0

@[expose] noncomputable def stepN (R : List Nat) (k : List Nat → Bool) (op : Op) : Bool :=
  Op.rec (motive := fun _ => Bool)
    (fun i j t => forceB (O.mul (getN R i) (getN R j)) fun a => forceL (R.set t a) k)
    (fun e i t => forceB (powN O (Nat.succ e) (getN R i) e) fun a => forceL (R.set t a) k) op

@[expose] noncomputable def runN (prog : List Op) : List Nat → (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => List Nat → (List Nat → Bool) → Bool)
    (fun R k => k R) (fun op _ ih R k => stepN O R (fun R' => ih R' k) op) prog

@[expose] noncomputable def initN (A B n : Nat) : List Nat :=
  (List.range n).map fun r => if r = 0 then A else if r = 1 then B else O.one

@[expose] noncomputable def regsN (A B n : Nat) (prog : List Op) (k : List Nat → Bool) : Bool :=
  runN O prog (initN O A B n) k

@[expose] noncomputable def evalWN (R : List Nat) : Word → Nat
  | [] => O.one
  | (r, e) :: w => O.mul (powN O (Nat.succ e) (getN R r) e) (evalWN R w)

@[expose] noncomputable def factN (R : List Nat) (n : Nat) : MFact → Bool
  | .ord r e => decide (r < n) && decide (0 < e) &&
      O.eq (powN O (Nat.succ e) (getN R r) e) O.one
  | .conj h u w => decide (h < n) && wordLt n u && wordLt n w &&
      O.eq (O.mul (getN R h) (evalWN O R u)) (O.mul (evalWN O R w) (getN R h))
  | .ne w₁ w₂ t => wordLt n w₁ && wordLt n w₂ &&
      O.vne (O.vmul (O.unit t) (evalWN O R w₁)) (O.vmul (O.unit t) (evalWN O R w₂))
  | .eq w₁ w₂ => wordLt n w₁ && wordLt n w₂ && O.eq (evalWN O R w₁) (evalWN O R w₂)

@[expose] noncomputable def certN (R : List Nat) (C : MCert) : Bool :=
  decide (2 ≤ C.nregs) && C.prog.all (Op.lt C.nregs) && C.facts.all (factN O R C.nregs)

@[expose] noncomputable def mcertN (A B : Nat) (C : MCert) : Bool :=
  regsN O A B C.nregs C.prog fun R => certN O R C

@[expose] def letterN (g gi : Nat → Nat) (l : Int) : Nat :=
  if 0 < l then g (l.toNat - 1) else gi ((-l).toNat - 1)

@[expose] noncomputable def wordFromN (g gi : Nat → Nat) (w : List Int) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun X => X)
    (fun l _ ih X => CFSG.KC.Loop.strictN (O.mul X (letterN g gi l)) ih) w

@[expose] noncomputable def powL (X : Nat) : Nat → Nat
  | 0 => O.one
  | e + 1 => O.mul (powL X e) X

@[expose] noncomputable def chunkN (A B : Nat) (C : MCert) (k i : Nat) : Bool :=
  regsN O A B C.nregs C.prog fun R => ((C.facts.drop (i * k)).take k).all (factN O R C.nregs)

end CFSG.KC.OpsMN

end
