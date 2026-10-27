module

public import Certificates.Data.Kernel.L34Cov.Alpha
public import Certificates.Data.Kernel.L34W.Model

public section

namespace CFSG.KC.L34Cov

open CFSG.KC CFSG.KC.Loop CFSG.KC.L34W

@[expose] noncomputable def t1colOK (V : Nat) (TA TB T : Nat → Nat) (C : List (List Nat))
    (k g : Nat) : Bool :=
  bindB (ent T k g) fun e =>
    cvIdOK V TA TB (C.getD k [] ++ C.getD g [] ++ invW (C.getD (Nat.div e 48) []))
      (Nat.div (Nat.mod e 48) 12) (Nat.div (Nat.mod e 12) 3) (Nat.mod e 3)

@[expose] noncomputable def t1colsOK (V : Nat) (TA TB T : Nat → Nat) (C : List (List Nat))
    (k : Nat) : Bool :=
  andB (t1colOK V TA TB T C k 1) (andB (t1colOK V TA TB T C k 2)
    (andB (t1colOK V TA TB T C k 16) (t1colOK V TA TB T C k 20)))

@[expose] noncomputable def t1zeroOK (T : Nat → Nat) (k : Nat) : Bool :=
  Nat.beq (ent T k 0) (Nat.mul 48 k)

@[expose] noncomputable def zEqOK (a b c d : Nat) : Bool :=
  andB (Nat.beq (Nat.mod (Nat.add (Nat.div (Nat.mod a 48) 12) (Nat.div (Nat.mod b 48) 12)) 4)
      (Nat.mod (Nat.add (Nat.div (Nat.mod c 48) 12) (Nat.div (Nat.mod d 48) 12)) 4))
    (andB (Nat.beq (Nat.mod (Nat.add (Nat.div (Nat.mod a 12) 3) (Nat.div (Nat.mod b 12) 3)) 4)
        (Nat.mod (Nat.add (Nat.div (Nat.mod c 12) 3) (Nat.div (Nat.mod d 12) 3)) 4))
      (Nat.beq (Nat.mod (Nat.add (Nat.mod a 3) (Nat.mod b 3)) 3)
        (Nat.mod (Nat.add (Nat.mod c 3) (Nat.mod d 3)) 3)))

@[expose] noncomputable def t1clOK (T : Nat → Nat) (k l g : Nat) : Bool :=
  bindB (ent T k l) fun a => bindB (ent T (Nat.div a 48) g) fun b =>
  bindB (ent T l g) fun c => bindB (ent T k (Nat.div c 48)) fun d =>
    andB (Nat.beq (Nat.div b 48) (Nat.div d 48)) (zEqOK a b d c)

@[expose] noncomputable def t1clsOK (T : Nat → Nat) (k l : Nat) : Bool :=
  andB (t1clOK T k l 1) (andB (t1clOK T k l 2) (andB (t1clOK T k l 16) (t1clOK T k l 20)))

@[expose] noncomputable def imgBits (T : Nat → Nat) (l : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.shiftLeft 1 (Nat.div (ent T l 1) 48)) (Nat.shiftLeft 1 (Nat.div (ent T l 2) 48)))
    (Nat.lor (Nat.shiftLeft 1 (Nat.div (ent T l 16) 48)) (Nat.shiftLeft 1 (Nat.div (ent T l 20) 48)))

@[expose] noncomputable def stepM (T : Nat → Nat) (M : Nat) : Nat :=
  (List.range 64).foldl (fun acc l => cond (Nat.testBit M l) (Nat.lor acc (imgBits T l)) acc) M

@[expose] noncomputable def reachM (T : Nat → Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => stepM T (reachM T n)

end CFSG.KC.L34Cov

end
