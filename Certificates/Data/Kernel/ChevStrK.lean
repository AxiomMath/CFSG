module

public import Init

public section

namespace CFSG.KC.ChevStr

@[expose] noncomputable def allN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i acc => Bool.rec (motive := fun _ => Bool) false (f i) acc) n

@[expose] noncomputable def orB (a b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) b true a

@[expose] noncomputable def andB (a b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def eqB (a b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false b) b a

@[expose] def dig (c j : Nat) : Nat :=
  Nat.mod (Nat.div c (Nat.pow 16 j)) 16

@[expose] def lane (X k : Nat) : Nat :=
  Nat.mod (Nat.div X (Nat.pow 4294967296 k)) 4294967296

@[expose] def lane8 (X k : Nat) : Nat :=
  Nat.mod (Nat.div X (Nat.pow 256 k)) 256

@[expose] noncomputable def lenL (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ n => Nat.succ n) L

@[expose] noncomputable def pack (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun a _ acc => Nat.add a (Nat.mul 4294967296 acc)) L

@[expose] noncomputable def verL (X : Nat) (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun a _ ih k => andB (Nat.beq (lane X k) a) (ih (Nat.succ k))) L

@[expose] def key (r P x : Nat) : Nat :=
  Nat.mod (Nat.mod x (Nat.pow 16 r)) P

@[expose] noncomputable def hashT (r P : Nat) (L : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun a _ ih k => Nat.add (Nat.mul (Nat.succ k) (Nat.pow 256 (key r P a))) (ih (Nat.succ k))) L

@[expose] noncomputable def basisLike (r c i e : Nat) : Bool :=
  allN r fun j => Nat.beq (dig c j) (Bool.rec (motive := fun _ => Nat) 8 e (Nat.beq j i))

@[expose] noncomputable def lookup (r P len R T x : Nat) : Bool :=
  (fun y => (fun j => andB (andB (Nat.blt 0 j) (Nat.ble j len))
      (Nat.beq (Nat.mod (lane R (Nat.pred j)) (Nat.pow 16 r)) y))
    (lane8 T (Nat.mod y P))) (Nat.mod x (Nat.pow 16 r))

@[expose] noncomputable def strOK (r P len W R T c s i : Nat) : Bool :=
  (fun d u q => andB (Nat.ble (Nat.add u q) 3)
    (allN (Nat.add (Nat.mul 2 W) 1) fun n => (fun t => eqB
      (andB (andB (Nat.ble W t) (Nat.blt t (Nat.add W 16)))
        (lookup r P len R T (Nat.add (Nat.sub c (Nat.mul d (Nat.pow 16 i)))
          (Nat.mul (Nat.sub t W) (Nat.pow 16 i)))))
      (andB (Nat.ble W (Nat.add n q)) (Nat.ble n (Nat.add W u)))) (Nat.add d n)))
    (dig c i) (Nat.div (dig s i) 4) (Nat.mod (dig s i) 4)

@[expose] noncomputable def mainK (r P len W R SL T : Nat) : Bool :=
  allN len fun k => (fun c s => allN r fun i =>
    orB (orB (basisLike r c i 9) (basisLike r c i 7)) (strOK r P len W R T c s i))
    (lane R k) (lane SL k)

@[expose] noncomputable def top (r P W : Nat) (roots strings : List Nat) : Bool :=
  (fun len R SL T =>
    andB (andB (andB (andB (verL R roots 0) (verL SL strings 0)) (Nat.beq (lenL strings) len))
      (allN len fun k => Nat.beq (lane8 T (key r P (lane R k))) (Nat.succ k)))
      (mainK r P len W R SL T))
    (lenL roots) (pack roots) (pack strings) (hashT r P roots 0)

@[expose] noncomputable def coordsK (r M : Nat) (roots : List Nat) : Bool :=
  (fun R => andB (verL R roots 0) (allN (lenL roots) fun k => (fun c => allN r fun j =>
      andB (Nat.ble 8 (Nat.add (dig c j) M)) (Nat.ble (dig c j) (Nat.add 8 M))) (lane R k)))
    (pack roots)

end CFSG.KC.ChevStr

end
