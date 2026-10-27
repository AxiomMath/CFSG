module

public section

namespace CFSG.KD.G24Lin

@[expose] def bitK (x i : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight x i) 1) 1

@[expose] def xorK (x : Nat) (F : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun c acc => cond (bitK x c) (Nat.xor acc (F c)) acc) n

@[expose] def spanK (D : Nat → Nat) (np nc nr : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun a acc => acc && Nat.beq
      (Nat.xor (xorK (D (Nat.add (Nat.add np nc) a)) (fun r => D (Nat.add (Nat.add np (Nat.add nc nc)) r)) nr)
        (xorK (D (Nat.add np a)) D np))
      (Nat.shiftLeft 1 a)) nc

@[expose] noncomputable def packC (l : List Char) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun c _ acc => Nat.add (cond (Nat.beq c.toNat 49) 1 0) (Nat.mul 2 acc)) l

@[expose] noncomputable def rowsK (D : Nat → Nat) (o : Nat) (L : List (List Char)) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun l _ ih i => Nat.beq (D i) (packC l) && ih (Nat.succ i)) L o

@[expose] def laneK (X k : Nat) : Nat := Nat.land (Nat.shiftRight X (Nat.mul 16 k)) 65535

@[expose] def wvK (RC n g T : Nat) : Nat := xorK T (fun c => laneK RC (Nat.add (Nat.mul g n) c)) n

end CFSG.KD.G24Lin

end
