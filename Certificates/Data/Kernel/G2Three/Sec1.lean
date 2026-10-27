module

public import Certificates.Data.Kernel.G2Three.Defs

public section

namespace CFSG.KD.G2Three.Sec1

open CFSG.KC.Ord CFSG.KC.Loop CFSG.KD.G2Three

@[expose] noncomputable def LP : Nat := Nat.sub (Nat.shiftLeft 1 392) 1

@[expose] noncomputable def ONEP : Nat := Nat.add ONE (Nat.shiftLeft ONE 392)

@[expose] noncomputable def MULP (a b : Nat) : Nat :=
  Nat.add (MUL (Nat.land a LP) (Nat.land b LP))
    (Nat.shiftLeft (MUL (Nat.shiftRight a 392) (Nat.shiftRight b 392)) 392)

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def allR (k : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun s ih => bAnd(f s, ih)) k

@[expose] noncomputable def parK (PA PB POS : Nat → Nat) (k m hi : Nat) : Bool :=
  allBelow m hi fun i =>
    bAnd(Nat.ble (PA i) i, bAnd(Nat.blt (PB i) k,
      Nat.beq (POS (Nat.add (Nat.mul (PA i) k) (PB i))) (Nat.succ i)))

@[expose] noncomputable def closP (X G POS : Nat → Nat) (n k lo m hi : Nat) : Bool :=
  allBelow m hi fun j => (fun i =>
    bAnd(Nat.blt (POS i) n, Nat.beq (X (POS i)) (MULP (X (Nat.div i k)) (G (Nat.mod i k)))))
    (Nat.add lo j)

@[expose] noncomputable def pwP (G : Nat → Nat) (r c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ONEP
    (fun i acc => nIf(Nat.blt 0 (Nat.land c (Nat.shiftLeft 1 i)), MULP acc (G i), acc)) r

@[expose] noncomputable def basisK (X G : Nat → Nat) (r n hi : Nat) : Bool :=
  allBelow n hi fun c => Nat.beq (X c) (pwP G r c)

@[expose] noncomputable def eqK (A B C D : Nat → Nat) (m hi : Nat) : Bool :=
  allBelow m hi fun q => Nat.beq (MULP (A q) (B q)) (MULP (C q) (D q))

@[expose] noncomputable def neK (A B C D : Nat → Nat) (m hi : Nat) : Bool :=
  allBelow m hi fun q => Bool.not' (Nat.beq (MULP (A q) (B q)) (MULP (C q) (D q)))

@[expose] noncomputable def idxK (X Y I : Nat → Nat) (n m hi : Nat) : Bool :=
  allBelow m hi fun q => bAnd(Nat.blt (I q) n, Nat.beq (X (I q)) (Y q))

@[expose] noncomputable def ltK (I : Nat → Nat) (n m hi : Nat) : Bool :=
  allBelow m hi fun q => Nat.blt (I q) n

@[expose] noncomputable def neqK (U V : Nat → Nat) (m hi : Nat) : Bool :=
  allBelow m hi fun q => Bool.not' (Nat.beq (U q) (V q))

@[expose] noncomputable def actK (X G M : Nat → Nat) (k hi : Nat) : Bool :=
  allBelow (Nat.mul 3 k) hi fun q => (fun s j =>
    Nat.beq (MULP (G s) (X (Nat.shiftLeft 1 j)))
      (MULP (X (fld(M s, Nat.mul 3 j, 7))) (G s))) (Nat.div q 3) (Nat.mod q 3)

@[expose] noncomputable def cntK (X G : Nat → Nat) (k n hi : Nat) : Nat :=
  sumBelow n hi fun i => strictN (X i) fun x =>
    nIf(allR k fun s => Nat.beq (MULP x (G s)) (MULP (G s) x), 1, 0)

@[expose] noncomputable def sqInK (X Y IQ : Nat → Nat) (nY n hi : Nat) : Bool :=
  allBelow n hi fun i => strictB (MULP (X i) (X i)) fun q =>
    bIf(Nat.beq (MULP q q) ONEP, bAnd(Nat.blt (IQ i) nY, Nat.beq (Y (IQ i)) q), true)

@[expose] noncomputable def spanM (a b : Nat) : Nat :=
  Nat.lor (Nat.lor 1 (Nat.shiftLeft 1 a)) (Nat.lor (Nat.shiftLeft 1 b) (Nat.shiftLeft 1 (Nat.xor a b)))

@[expose] noncomputable def colC (M v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun k acc => nIf(Nat.blt 0 (Nat.land v (Nat.shiftLeft 1 k)), Nat.xor acc (fld(M, Nat.mul 3 k, 7)),
      acc)) 3

@[expose] noncomputable def MUL9 (M N : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j acc => Nat.lor acc (Nat.shiftLeft (colC M (fld(N, Nat.mul 3 j, 7))) (Nat.mul 3 j))) 3

@[expose] noncomputable def clos9 (X G POS : Nat → Nat) (n k hi : Nat) : Bool :=
  allBelow (Nat.mul n k) hi fun i =>
    bAnd(Nat.blt (POS i) n, Nat.beq (X (POS i)) (MUL9 (X (Nat.div i k)) (G (Nat.mod i k))))

end CFSG.KD.G2Three.Sec1

end
