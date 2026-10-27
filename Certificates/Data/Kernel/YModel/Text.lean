module

public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.Common.Lce

public section

namespace CFSG.KC.YModel

open CFSG.KC

@[expose] noncomputable def decChunk (len : Nat) : Nat → List Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat → List Nat) (fun _ t => t)
    (fun _ ih N t => List.cons (Nat.land N (nat_lit 255)) (ih (Nat.shiftRight N (nat_lit 8)) t)) len

@[expose] noncomputable def bytesOf (L : List (Nat × Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun p _ ih => Prod.rec (motive := fun _ => List Nat) (fun N len => decChunk len N ih) p) L

@[expose] noncomputable def decChunkC (len : Nat) : Nat → List Char → List Char :=
  Nat.rec (motive := fun _ => Nat → List Char → List Char) (fun _ t => t)
    (fun _ ih N t => List.cons (Char.ofNat (Nat.land N (nat_lit 255)))
      (ih (Nat.shiftRight N (nat_lit 8)) t)) len

@[expose] noncomputable def charsOf (L : List (Nat × Nat)) : List Char :=
  List.rec (motive := fun _ => List Char) List.nil
    (fun p _ ih => Prod.rec (motive := fun _ => List Char) (fun N len => decChunkC len N ih) p) L

@[expose] noncomputable def decV (c : Nat) : Nat :=
  nIf(Nat.blt c (nat_lit 48), nat_lit 10, nIf(Nat.blt c (nat_lit 58), Nat.sub c (nat_lit 48), nat_lit 10))

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def tokCode (sgn L v ng : Nat) : Nat :=
  nIf(Nat.blt L sgn, v, Nat.add (Nat.mul (nat_lit 2) v) ng)

@[expose] noncomputable def lhead (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun a _ _ => a) l

@[expose] noncomputable def ltail (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun _ t _ => t) l

@[expose] noncomputable def lnil (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l

@[expose] noncomputable def joinW (w : Nat) (cs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c _ ih => Nat.lor c (Nat.shiftLeft ih (Nat.mul (nat_lit 32) w))) cs

@[expose] noncomputable def tokEnd (w lines : Nat) (C : Nat → List Nat) (E : Nat → Nat) (nl : Bool)
    (L e t x cur j : Nat) (rest : List Nat)
    (k : Nat → Nat → Nat → Nat → List Nat → Bool) : Bool :=
  bAnd(Nat.blt (nat_lit 0) t, bAnd(Nat.blt x (Nat.shiftLeft (nat_lit 1) w),
    bAnd(Nat.beq x (Nat.land cur (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))),
    strictB (Nat.succ e) (fun e' => strictB (Nat.succ j) (fun j' =>
      strictB (Nat.shiftRight cur w) (fun cr =>
      Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) (k L e' cr j' rest)
          (bAnd(Nat.beq cr (nat_lit 0), k L e' (lhead rest) (nat_lit 0) (ltail rest)))
          (Nat.beq j' (nat_lit 32)))
        (bAnd(Nat.blt L lines, bAnd(Nat.beq e' (E L), bAnd(Nat.beq cr (nat_lit 0),
          bAnd(lnil rest, strictB (Nat.succ L) (fun L' =>
            k L' (nat_lit 0) (lhead (C L')) (nat_lit 0) (ltail (C L'))))))))
        nl))))))

@[expose] noncomputable def decRun (w lines sgn : Nat) (C : Nat → List Nat) (E : Nat → Nat)
    (bs : List Nat) : Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → Bool)
    (fun L _ t _ ng _ _ _ => bAnd(Nat.beq L lines, bAnd(Nat.beq t (nat_lit 0), Nat.beq ng (nat_lit 0))))
    (fun c _ ih L e t v ng cur j rest => strictB (decV c) (fun d =>
      bIf(Nat.blt d (nat_lit 10),
        strictB (Nat.add (Nat.mul v (nat_lit 10)) d) (fun v' =>
          strictB (Nat.succ t) (fun t' => ih L e t' v' ng cur j rest)),
      bIf(Nat.beq c (nat_lit 45),
        bAnd(Nat.ble sgn L, bAnd(Nat.beq t (nat_lit 0), bAnd(Nat.beq ng (nat_lit 0),
          ih L e t v (nat_lit 1) cur j rest))),
      bIf(Nat.beq c (nat_lit 32),
        tokEnd w lines C E false L e t (tokCode sgn L v ng) cur j rest
          (fun L' e' cur' j' rest' => ih L' e' (nat_lit 0) (nat_lit 0) (nat_lit 0) cur' j' rest'),
      bIf(Nat.beq c (nat_lit 10),
        tokEnd w lines C E true L e t (tokCode sgn L v ng) cur j rest
          (fun L' e' cur' j' rest' => ih L' e' (nat_lit 0) (nat_lit 0) (nat_lit 0) cur' j' rest'),
        false))))))
    bs

@[expose] noncomputable def decBind (bs : List Nat) (w lines sgn : Nat) (C : Nat → List Nat)
    (E : Nat → Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) w, bAnd(Nat.ble w (nat_lit 32),
    decRun w lines sgn C E bs (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0)
      (lhead (C 0)) (nat_lit 0) (ltail (C 0))))

@[expose] noncomputable def fieldAt (w F i : Nat) : Nat :=
  Nat.land (Nat.shiftRight F (Nat.mul w i)) (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))

@[expose] noncomputable def lgetL (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun a _ ih j => Nat.rec (motive := fun _ => List Nat) a (fun j' _ => ih j') j) l i

@[expose] noncomputable def lget (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun a _ ih j => Nat.rec (motive := fun _ => Nat) a (fun j' _ => ih j') j) l i

end CFSG.KC.YModel

end
