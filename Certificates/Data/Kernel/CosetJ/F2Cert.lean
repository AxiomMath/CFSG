module

public import Init

public section

namespace CFSG.KC.CosetJ.F2

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec false b a

@[expose] noncomputable def getL (L : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun h _ ih i => Nat.rec (motive := fun _ => Nat) h (fun j _ => ih j) i) L

@[expose] noncomputable def bit (x i : Nat) : Nat := Nat.land (Nat.shiftRight x i) (nat_lit 1)

@[expose] noncomputable def xorN (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k ih => Nat.xor (f k) ih) n

@[expose] noncomputable def col (a : List Nat) (j : Nat) : Nat := Nat.land (getL a j) (nat_lit 2047)

@[expose] noncomputable def mulV (a : List Nat) (x : Nat) : Nat :=
  xorN (nat_lit 11) fun v => Nat.mul (bit x v) (col a v)

@[expose] noncomputable def e2 (i j : Nat) : Nat :=
  Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.mul (nat_lit 11) i) j)

@[expose] noncomputable def rowSym (q : Nat) : Nat :=
  Nat.xor (e2 (Nat.div q (nat_lit 11)) (Nat.mod q (nat_lit 11)))
    (e2 (Nat.mod q (nat_lit 11)) (Nat.div q (nat_lit 11)))

@[expose] noncomputable def rowDiag (q : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0)
    (e2 (Nat.div q (nat_lit 11)) (Nat.mod q (nat_lit 11)))
    (Nat.beq (Nat.div q (nat_lit 11)) (Nat.mod q (nat_lit 11)))

@[expose] noncomputable def rowInv (a : List Nat) (q : Nat) : Nat :=
  Nat.xor
    (xorN (nat_lit 11) fun u => Nat.mul (bit (col a (Nat.div q (nat_lit 11))) u)
      (Nat.shiftLeft (col a (Nat.mod q (nat_lit 11))) (Nat.mul (nat_lit 11) u)))
    (e2 (Nat.div q (nat_lit 11)) (Nat.mod q (nat_lit 11)))

@[expose] noncomputable def spread (S : List Nat) (q R w : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun s _ ih r => Bool.rec (motive := fun _ => Nat) (ih (Nat.succ r))
      (Nat.xor (Nat.mul (bit s q) (Nat.shiftLeft R (Nat.mul w r))) (ih (Nat.succ r)))
      (Nat.blt r (nat_lit 121)))
    S (nat_lit 0)

@[expose] noncomputable def idPack (n w : Nat) : Nat :=
  xorN n fun r => Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.mul w r) r)

@[expose] noncomputable def formOK (S₁ S₂ S₃ S₄ a b : List Nat) : Bool :=
  Nat.beq
    (xorN (nat_lit 121) fun q =>
      Nat.xor (spread S₁ q (rowSym q) (nat_lit 121))
        (Nat.xor (spread S₂ q (rowDiag q) (nat_lit 121))
          (Nat.xor (spread S₃ q (rowInv a q) (nat_lit 121))
            (spread S₄ q (rowInv b q) (nat_lit 121)))))
    (idPack (nat_lit 121) (nat_lit 121))

@[expose] noncomputable def foxW (a b : List Nat) (w : List Bool) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x
    (fun c _ ih => (fun y F =>
      Nat.add (Bool.rec (motive := fun _ => Nat) (mulV a y) (mulV b y) c)
        (Nat.shiftLeft
          (Nat.xor F (Bool.rec (motive := fun _ => Nat) y (Nat.shiftLeft y (nat_lit 11)) c))
          (nat_lit 11)))
      (Nat.land ih (nat_lit 2047)) (Nat.shiftRight ih (nat_lit 11))) w

@[expose] noncomputable def rowFox (a b : List Nat) (ws : List (List Bool)) (q : Nat) : Nat :=
  Nat.shiftRight
    (foxW a b
      (List.rec (motive := fun _ => Nat → List Bool) (fun _ => [])
        (fun h _ ih i => Nat.rec (motive := fun _ => List Bool) h (fun j _ => ih j) i) ws
        (Nat.div q (nat_lit 11)))
      (Nat.shiftLeft (nat_lit 1) (Nat.mod q (nat_lit 11))))
    (nat_lit 11)

@[expose] noncomputable def rowDelta (a b : List Nat) (r : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Nat.xor (col b (Nat.sub r (nat_lit 11))) (Nat.shiftLeft (nat_lit 1) (Nat.sub r (nat_lit 11))))
    (Nat.xor (col a r) (Nat.shiftLeft (nat_lit 1) r)) (Nat.blt r (nat_lit 11))

@[expose] noncomputable def spreadY (Y : List Nat) (q R : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun s _ ih r => Bool.rec (motive := fun _ => Nat) (ih (Nat.succ r))
      (Nat.xor (Nat.mul (bit s q) (Nat.shiftLeft R (Nat.mul (nat_lit 22) r))) (ih (Nat.succ r)))
      (Nat.blt r (nat_lit 22)))
    Y (nat_lit 0)

@[expose] noncomputable def foxOK (X Y a b : List Nat) (ws : List (List Bool)) : Bool :=
  Nat.beq
    (Nat.xor
      (xorN (nat_lit 22) fun r => Nat.shiftLeft
        (xorN (nat_lit 11) fun j =>
          Nat.mul (bit (rowDelta a b r) j) (Nat.land (getL X j) (nat_lit 4194303)))
        (Nat.mul (nat_lit 22) r))
      (xorN (nat_lit 66) fun q => spreadY Y q (rowFox a b ws q)))
    (idPack (nat_lit 22) (nat_lit 22))

end CFSG.KC.CosetJ.F2

end
