module

public import Certificates.Data.Kernel.OpsMcertN

public section

namespace CFSG.KC.OpsMT

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.KC.OpsK CFSG.KC.OpsMN

inductive RT where
  | leaf : RT
  | node : RT → Nat → RT → RT

@[expose] noncomputable def getR (T : RT) : Nat → Nat :=
  RT.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ x _ ihl ihr i => Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (ihr (Nat.div (Nat.sub i 1) 2))
        (ihl (Nat.div (Nat.sub i 1) 2)) (Nat.beq (Nat.mod i 2) 1))
      x (Nat.beq i 0)) T

@[expose] noncomputable def domR (T : RT) : Nat → Bool :=
  RT.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun _ _ _ ihl ihr i => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (ihr (Nat.div (Nat.sub i 1) 2))
        (ihl (Nat.div (Nat.sub i 1) 2)) (Nat.beq (Nat.mod i 2) 1))
      true (Nat.beq i 0)) T

@[expose] noncomputable def setR (T : RT) (t a : Nat) : RT :=
  RT.rec (motive := fun _ => Nat → RT) (fun _ => RT.leaf)
    (fun l x r ihl ihr i => Bool.rec (motive := fun _ => RT)
      (Bool.rec (motive := fun _ => RT) (RT.node l x (ihr (Nat.div (Nat.sub i 1) 2)))
        (RT.node (ihl (Nat.div (Nat.sub i 1) 2)) x r) (Nat.beq (Nat.mod i 2) 1))
      (RT.node l a r) (Nat.beq i 0)) T t

@[expose] noncomputable def setK (T : RT) (t a : Nat) (k : RT → Bool) : Bool :=
  RT.rec (motive := fun _ => Nat → (RT → Bool) → Bool) (fun _ k => k RT.leaf)
    (fun l x r ihl ihr i k => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (ihr (Nat.div (Nat.sub i 1) 2) fun r' => k (RT.node l x r'))
        (ihl (Nat.div (Nat.sub i 1) 2) fun l' => k (RT.node l' x r)) (Nat.beq (Nat.mod i 2) 1))
      (k (RT.node l a r)) (Nat.beq i 0)) T t k

@[expose] noncomputable def mkT (fuel : Nat) : Nat → (Nat → Nat) → RT :=
  Nat.rec (motive := fun _ => Nat → (Nat → Nat) → RT) (fun _ _ => RT.leaf)
    (fun _ ih n f => Bool.rec (motive := fun _ => RT)
      (RT.node (ih (Nat.div n 2) fun j => f (2 * j + 1)) (f 0)
        (ih (Nat.div (Nat.sub n 1) 2) fun j => f (2 * j + 2)))
      RT.leaf (Nat.beq n 0)) fuel

variable {V : Type} (O : Ops Nat V)

@[expose] noncomputable def stepT (T : RT) (k : RT → Bool) (op : Op) : Bool :=
  Op.rec (motive := fun _ => Bool)
    (fun i j t => forceB (O.mul (getR T i) (getR T j)) fun a => setK T t a k)
    (fun e i t => forceB (powN O (Nat.succ e) (getR T i) e) fun a => setK T t a k) op

@[expose] noncomputable def runT (prog : List Op) : RT → (RT → Bool) → Bool :=
  List.rec (motive := fun _ => RT → (RT → Bool) → Bool)
    (fun T k => k T) (fun op _ ih T k => stepT O T (fun T' => ih T' k) op) prog

@[expose] def initF (A B o : Nat) (r : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) o B (Nat.beq r 1)) A
    (Nat.beq r 0)

@[expose] noncomputable def regsT (A B n : Nat) (prog : List Op) (k : RT → Bool) : Bool :=
  forceB O.one fun o => runT O prog (mkT n n (initF A B o)) k

@[expose] noncomputable def evalWG (g : Nat → Nat) : Word → Nat
  | [] => O.one
  | (r, e) :: w => O.mul (powN O (Nat.succ e) (g r) e) (evalWG g w)

@[expose] noncomputable def factG (g : Nat → Nat) (n : Nat) : MFact → Bool
  | .ord r e => decide (r < n) && decide (0 < e) &&
      O.eq (powN O (Nat.succ e) (g r) e) O.one
  | .conj h u w => decide (h < n) && wordLt n u && wordLt n w &&
      O.eq (O.mul (g h) (evalWG O g u)) (O.mul (evalWG O g w) (g h))
  | .ne w₁ w₂ t => wordLt n w₁ && wordLt n w₂ &&
      O.vne (O.vmul (O.unit t) (evalWG O g w₁)) (O.vmul (O.unit t) (evalWG O g w₂))
  | .eq w₁ w₂ => wordLt n w₁ && wordLt n w₂ && O.eq (evalWG O g w₁) (evalWG O g w₂)

@[expose] noncomputable def certG (g : Nat → Nat) (C : MCert) : Bool :=
  decide (2 ≤ C.nregs) && C.prog.all (Op.lt C.nregs) && C.facts.all (factG O g C.nregs)

@[expose] noncomputable def mcertT (A B : Nat) (C : MCert) : Bool :=
  regsT O A B C.nregs C.prog fun T => certG O (getR T) C

@[expose] noncomputable def seedsT (A B n : Nat) (prog : List Op) (fs : List MFact)
    (rA rB : Nat) : Bool :=
  regsT O A B n prog fun T => certG O (getR T) ⟨n, prog, fs⟩ && O.eq (getR T rA) A &&
    O.eq (getR T rB) B

end CFSG.KC.OpsMT

end
