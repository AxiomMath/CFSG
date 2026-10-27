module

public import Certificates.Data.Kernel.ONanF2K.Defs

public section

namespace CFSG.KC.ONanF2

open CFSG.OddStandard.ONanRec.F2 CFSG.KC.ONanF2K

@[expose] def enc (x : AlpE) : ℕ :=
  Nat.add (Nat.mul 64 x.d.val)
    (Nat.add (Nat.mul 16 (ZMod.val x.v0)) (Nat.add (Nat.mul 4 (ZMod.val x.v1)) (ZMod.val x.v2)))

@[expose] def dec (c : ℕ) : AlpE := decN c

@[expose] def cmK (a b : ℕ) : Bool := Nat.beq (mulK a b) (mulK b a)

@[expose] def bitB (m c : ℕ) : Bool := Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 c))

@[expose] def setB (m c : ℕ) : ℕ := Nat.lor m (Nat.shiftLeft 1 c)

@[expose] def diffM (a b : ℕ) : ℕ := Nat.xor a (Nat.land a b)

@[expose] noncomputable def allB (q : ℕ → Bool) (k : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun c acc => Bool.rec false acc (q c)) k

@[expose] noncomputable def maskOf (q : ℕ → Bool) (k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun c acc => Bool.rec acc (setB acc c) (q c)) k

@[expose] noncomputable def cntQ (q : ℕ → Bool) (k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun c acc => Bool.rec acc (Nat.succ acc) (q c)) k

@[expose] def iffB (a b : Bool) : Bool := Bool.rec (Bool.rec true false b) b a

@[expose] noncomputable def allL (l : List ℕ) (q : ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun z _ r => Bool.rec false r (q z)) l

@[expose] def dC (c : ℕ) : ℕ := Nat.shiftRight c 6

@[expose] def ordB8 (d x2 x4 x8 : ℕ) : Bool :=
  (!Nat.beq d 0 || Nat.beq x4 0) &&
  ((!Nat.beq d 1 && !Nat.beq d 3) || (Nat.beq (mulK x8 x8) 0 && !Nat.beq x8 0)) &&
  (Nat.beq d 0 || Nat.beq d 1 || Nat.beq d 3 || Nat.beq x8 0) &&
  ((!Nat.beq d 2 && !Nat.beq d 4 && !Nat.beq d 6) || !Nat.beq x4 0 || Nat.beq x2 0 ||
    Nat.beq x2 34) &&
  (!Nat.beq d 5 || !Nat.beq x4 0 || Nat.beq x2 0 || Nat.beq x2 40) &&
  (!Nat.beq d 7 || !Nat.beq x4 0 || Nat.beq x2 0 || Nat.beq x2 10)

@[expose] def ordB4 (d x2 x4 : ℕ) : Bool := ordB8 d x2 x4 (mulK x4 x4)

@[expose] def ordB2 (d x2 : ℕ) : Bool := ordB4 d x2 (mulK x2 x2)

@[expose] def ordB (c : ℕ) : Bool := ordB2 (dC c) (mulK c c)

@[expose] noncomputable def cntM (M k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun c acc => Bool.rec acc (Nat.succ acc) (bitB M c)) k

@[expose] noncomputable def lorL (l : List ℕ) (acc : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) acc (fun y _ r => setB r y) l

@[expose] noncomputable def imgM (nxt : ℕ → List ℕ) (F k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun c acc => Bool.rec acc (lorL (nxt c) acc) (bitB F c)) k

@[expose] noncomputable def newM (nxt : ℕ → List ℕ) (F V : ℕ) : ℕ :=
  diffM (imgM nxt F 512) V

@[expose] def bfsStep (ih : ℕ → ℕ → ℕ) (V N : ℕ) : ℕ :=
  Bool.rec (ih (Nat.lor V N) N) V (Nat.beq N 0)

@[expose] noncomputable def bfsM (nxt : ℕ → List ℕ) (n : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun V _ => V)
    (fun _ ih V F => bfsStep ih V (newM nxt F V)) n

@[expose] def rmulK (gens : List ℕ) (c : ℕ) : List ℕ := gens.map (mulK c ·)

@[expose] def conjK (ps : List (ℕ × ℕ)) (c : ℕ) : List ℕ :=
  ps.flatMap fun p => [mulK (mulK p.2 c) p.1, mulK (mulK p.1 c) p.2]

@[expose] noncomputable def subB (gens : List ℕ) (M n : ℕ) : Bool :=
  Nat.beq (bfsM (rmulK gens) 64 1 1) M && Nat.beq (cntM M 512) n &&
    Nat.beq (newM (rmulK gens) M M) 0

@[expose] noncomputable def clsB (ps : List (ℕ × ℕ)) (r M : ℕ) : Bool :=
  Nat.beq (bfsM (conjK ps) 64 (setB 0 r) (setB 0 r)) M

@[expose] noncomputable def clsOKB (ps : List (ℕ × ℕ)) (r M n : ℕ) : Bool :=
  clsB ps r M && Nat.beq (cntM M 512) n && Nat.beq (newM (conjK ps) M M) 0

@[expose] noncomputable def nvB (ps : List (ℕ × ℕ)) (L : List (ℕ × ℕ)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ r => Bool.rec false (Bool.rec false r (Nat.ble 16 (cntM p.2 512))) (clsB ps p.1 p.2))
    L

@[expose] noncomputable def lorP (L : List (ℕ × ℕ)) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun p _ r => Nat.lor p.2 r) L

end CFSG.KC.ONanF2
