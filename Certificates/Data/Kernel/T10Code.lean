module

public import Init

public section

namespace CFSG.KC.T10Code

@[expose] def tb (n i : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight n i) 1) 1

@[expose] def ALL : Nat := Nat.sub (Nat.shiftLeft 1 1024) 1

@[expose] noncomputable def allR (p : Nat → Bool) (lo N : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i acc => Bool.rec (motive := fun _ => Bool) false acc (p (Nat.add lo i))) N

@[expose] noncomputable def anyN (p : Nat → Bool) (N : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun i acc => Bool.rec (motive := fun _ => Bool) acc true (p i)) N

@[expose] noncomputable def cntN (p : Nat → Bool) (N : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc) (p i)) N

@[expose] noncomputable def plane (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun g acc => Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight g k) 1) g)) 1024

structure W10 where
  w0 : Nat
  w1 : Nat
  w2 : Nat
  w3 : Nat
  w4 : Nat
  w5 : Nat
  ws : Nat
  wa : Nat
  wb : Nat
  wc : Nat

@[expose] def mulW (p q : W10) : W10 :=
  let y0 := Nat.xor (Nat.xor q.w0 (Nat.land p.wa q.w1)) (Nat.land p.wb q.w2)
  let y1 := Nat.xor q.w1 (Nat.land p.wc q.w2)
  let y3 := Nat.xor (Nat.xor q.w3 (Nat.land p.wa q.w4)) (Nat.land p.wb q.w5)
  let y4 := Nat.xor q.w4 (Nat.land p.wc q.w5)
  ⟨Nat.xor (Nat.xor p.w0 y0) (Nat.land p.ws y3), Nat.xor (Nat.xor p.w1 y1) (Nat.land p.ws y4),
    Nat.xor (Nat.xor p.w2 q.w2) (Nat.land p.ws q.w5), Nat.xor p.w3 y3, Nat.xor p.w4 y4,
    Nat.xor p.w5 q.w5, Nat.xor p.ws q.ws, Nat.xor p.wa q.wa,
    Nat.xor (Nat.xor p.wb q.wb) (Nat.land p.wa q.wc), Nat.xor p.wc q.wc⟩

@[expose] def invW (p : W10) : W10 :=
  let b' := Nat.xor p.wb (Nat.land p.wa p.wc)
  let z0 := Nat.xor (Nat.xor p.w0 (Nat.land p.wa p.w1)) (Nat.land b' p.w2)
  let z1 := Nat.xor p.w1 (Nat.land p.wc p.w2)
  let z3 := Nat.xor (Nat.xor p.w3 (Nat.land p.wa p.w4)) (Nat.land b' p.w5)
  let z4 := Nat.xor p.w4 (Nat.land p.wc p.w5)
  ⟨Nat.xor z0 (Nat.land p.ws z3), Nat.xor z1 (Nat.land p.ws z4),
    Nat.xor p.w2 (Nat.land p.ws p.w5), z3, z4, p.w5, p.ws, p.wa, b', p.wc⟩

@[expose] def ZW : W10 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

@[expose] def difW (p q : W10) : Nat :=
  Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.xor p.w0 q.w0) (Nat.xor p.w1 q.w1))
    (Nat.lor (Nat.xor p.w2 q.w2) (Nat.xor p.w3 q.w3)))
    (Nat.lor (Nat.lor (Nat.xor p.w4 q.w4) (Nat.xor p.w5 q.w5)) (Nat.xor p.ws q.ws)))
    (Nat.lor (Nat.xor p.wa q.wa) (Nat.xor p.wb q.wb))) (Nat.xor p.wc q.wc)

@[expose] noncomputable def PL : W10 :=
  ⟨plane 0, plane 1, plane 2, plane 3, plane 4, plane 5, plane 6, plane 7, plane 8, plane 9⟩

@[expose] def bc (x k : Nat) : Nat := Nat.mul (Nat.land (Nat.shiftRight x k) 1) ALL

@[expose] def BC (x : Nat) : W10 :=
  ⟨bc x 0, bc x 1, bc x 2, bc x 3, bc x 4, bc x 5, bc x 6, bc x 7, bc x 8, bc x 9⟩

@[expose] def QMW (P : W10) : Nat := Nat.lor (Nat.lor P.ws P.wa) (Nat.lor P.wb P.wc)

@[expose] def SQW (P : W10) : Nat := difW (mulW P P) ZW

@[expose] def NZW (P : W10) : Nat := difW P ZW

@[expose] def CDW (P : W10) (x : Nat) : Nat := difW (mulW P (BC x)) (mulW (BC x) P)

@[expose] def CJW (P : W10) (x : Nat) : Nat :=
  difW (mulW (mulW (mulW P (BC x)) (invW P)) (BC 64))
    (mulW (BC 64) (mulW (mulW P (BC x)) (invW P)))

@[expose] def inQc (P : W10) (x : Nat) : Bool := !tb (QMW P) x

@[expose] def inMc (P : W10) (x : Nat) : Bool := !tb P.ws x

@[expose] def sq1c (P : W10) (x : Nat) : Bool := !tb (SQW P) x

@[expose] def isInvc (P : W10) (x : Nat) : Bool := !tb (SQW P) x && tb (NZW P) x

@[expose] def commc (P : W10) (g x : Nat) : Bool := !tb (CDW P x) g

@[expose] noncomputable def FB (P : W10) (x : Nat) : Bool :=
  inQc P x || !sq1c P x || inMc P x || cntN (fun g => inQc P g && commc P g x) 1024 != 16

@[expose] noncomputable def cTc (P : W10) : Nat := cntN (fun g => commc P g 64) 1024

@[expose] noncomputable def iTc (P : W10) : Nat :=
  cntN (fun g => commc P g 64 && isInvc P g) 1024

@[expose] noncomputable def FC (P : W10) (x : Nat) : Bool :=
  !inMc P x || inQc P x || !isInvc P x ||
    (let cx := cntN (fun g => commc P g x) 1024
     let ix := cntN (fun g => commc P g x && isInvc P g) 1024
     !(cx == 256 || (cx == 128 && ix == 55)) || anyN (fun g => !tb (CJW P x) g) 1024)

end CFSG.KC.T10Code
