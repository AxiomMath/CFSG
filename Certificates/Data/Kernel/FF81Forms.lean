module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.FF81F

@[expose] noncomputable def bitK (a t : Nat) : Bool := Nat.beq (fld(a, t, 1)) 1

@[expose] noncomputable def xorB (x y : Bool) : Bool := bIf(x, bIf(y, false, true), y)

@[expose] noncomputable def packK (f : Nat → Bool) (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun p acc => Nat.add acc (nIf(f p, Nat.pow 2 p, 0))) m

@[expose] noncomputable def entK (a b i j : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun k acc => xorB acc (bAnd(bitK a (Nat.add (Nat.mul 6 i) k), bitK b (Nat.add (Nat.mul 6 k) j))))
    6

@[expose] noncomputable def mulK (a b : Nat) : Nat :=
  packK (fun p => entK a b (Nat.div p 6) (Nat.mod p 6)) 36

@[expose] noncomputable def trK (a : Nat) : Nat :=
  packK (fun p => bitK a (Nat.add (Nat.mul 6 (Nat.mod p 6)) (Nat.div p 6))) 36

@[expose] noncomputable def ONEK : Nat := 34630287489

@[expose] noncomputable def J0K : Nat := 4328915976

@[expose] noncomputable def U0K : Nat := 38925369473

@[expose] noncomputable def ES : List Nat :=
  [66, 4100, 262152, 16777232, 1073741856, 8448, 524800, 33555456, 2147485696, 1081344,
    67174400, 4295098368, 138412032, 8598323200, 17716740096]

@[expose] noncomputable def gK (w Q : Nat) : Nat := Nat.xor (mulK (mulK (trK w) Q) w) Q

@[expose] noncomputable def fK (s w P : Nat) : Nat := gK w (mulK (mulK (trK s) P) s)

@[expose] noncomputable def linK (cs : List Nat) (n : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun c _ ih m => Nat.xor (nIf(bitK m 0, c, 0)) (ih (Nat.shiftRight m 1))) cs n

@[expose] noncomputable def colsK (s w : Nat) (cs es : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun es => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) es)
    (fun c _ ih es => List.rec (motive := fun _ => Bool) false
      (fun e es' _ => bAnd(Nat.beq c (fK s w e), ih es')) es) cs es

@[expose] noncomputable def pairOK (x : Nat × Nat × Nat × Nat × List Nat) : Bool :=
  bAnd(Nat.beq (mulK x.1 x.2.1) ONEK, bAnd(Nat.beq (mulK x.2.1 x.1) ONEK,
  bAnd(Nat.beq (mulK (mulK (trK x.1) J0K) x.1) J0K,
  bAnd(Nat.beq (mulK x.2.2.1 x.2.2.2.1) ONEK, bAnd(Nat.beq (mulK x.2.2.2.1 x.2.2.1) ONEK,
  bAnd(Nat.beq (mulK x.2.2.1 U0K) (mulK U0K x.2.2.1),
  bAnd(bIf(Nat.beq (mulK (mulK (trK x.2.2.1) J0K) x.2.2.1) J0K, false, true),
    colsK x.1 x.2.2.1 x.2.2.2.2 ES)))))))

@[expose] noncomputable def allPairs (PK : List (Nat × Nat × Nat × Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(pairOK x, ih)) PK

@[expose] noncomputable def colsAt (PK : List (Nat × Nat × Nat × Nat × List Nat)) (k : Nat) :
    List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih k => Nat.rec (motive := fun _ => List Nat) x.2.2.2.2 (fun k' _ => ih k') k) PK k

@[expose] noncomputable def lenP (PK : List (Nat × Nat × Nat × Nat × List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) PK

@[expose] noncomputable def okK (PK : List (Nat × Nat × Nat × Nat × List Nat)) (n k : Nat) :
    Bool :=
  bIf(Nat.beq n 2180, true, bAnd(Nat.blt k (lenP PK), Nat.beq (linK (colsAt PK k) n) 0))

@[expose] noncomputable def walkK (PK : List (Nat × Nat × Nat × Nat × List Nat)) (base : Nat)
    (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun k _ ih b => bAnd(okK PK b k, ih (Nat.succ b))) L base

@[expose] noncomputable def lenK (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) L

end CFSG.KC.FF81F

end
