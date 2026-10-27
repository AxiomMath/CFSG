module

public import Certificates.Data.CFSGNative.F3.Basic
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KS.F3L

open CFSG.F3.Native CFSG.KC.Enum

@[expose] noncomputable def strictT {α : Type} (y : Nat) (k : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def mk (d : Nat) : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) d) (nat_lit 1)

@[expose] noncomputable def blk (d : Nat) (L : V) (b : Nat) : V :=
  ⟨Nat.land (Nat.shiftRight L.p (Nat.mul d b)) (mk d), Nat.land (Nat.shiftRight L.m (Nat.mul d b)) (mk d)⟩

@[expose] noncomputable def unlane (d : Nat) (L : V) : Array V :=
  Array.ofFn (n := d) fun i => blk d L i.val

@[expose] noncomputable def spreadE (d nb : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (Nat.mul d b))) nb

@[expose] noncomputable def rmStep (E : Nat) (X y : V) (j : Nat) (acc : V) : V :=
  strictT (Nat.land (Nat.shiftRight X.p j) E) fun sp =>
  strictT (Nat.land (Nat.shiftRight (Nat.xor X.m (Nat.land X.m X.p)) j) E) fun sm =>
    acc.add ⟨Nat.lor (Nat.mul sp y.p) (Nat.mul sm y.m), Nat.lor (Nat.mul sp y.m) (Nat.mul sm y.p)⟩

@[expose] noncomputable def rmK (d E : Nat) (X : V) (Y : Nat → V) : V :=
  Nat.rec (motive := fun _ => V) V.zero
    (fun j acc => strictT acc.p fun ap => strictT acc.m fun am => rmStep E X (Y j) j ⟨ap, am⟩) d

@[expose] noncomputable def addW (a b : V) : V :=
  (fun t => (⟨Nat.xor (Nat.lor a.m b.m) t, Nat.xor (Nat.lor a.p b.p) t⟩ : V))
    (Nat.xor (Nat.lor a.p b.m) (Nat.lor a.m b.p))

@[expose] noncomputable def rmStepW (E : Nat) (X y : V) (j : Nat) (acc : V) : V :=
  (fun sp sm =>
      addW acc ⟨Nat.lor (Nat.mul sp y.p) (Nat.mul sm y.m), Nat.lor (Nat.mul sp y.m) (Nat.mul sm y.p)⟩)
    (Nat.land (Nat.shiftRight X.p j) E) (Nat.land (Nat.shiftRight X.m j) E)

@[expose] noncomputable def rmKW (d E : Nat) (X : V) (Y : Nat → V) : V :=
  Nat.rec (motive := fun _ => V) V.zero
    (fun j acc => strictT acc.p fun ap => strictT acc.m fun am => rmStepW E X (Y j) j ⟨ap, am⟩) d

@[expose] noncomputable def mulLane (d E : Nat) (X Y : V) : V :=
  Bool.rec (motive := fun _ => V) (rmK d E X (blk d Y))
    (strictT (Nat.xor X.m (Nat.land X.m X.p)) fun xm => rmKW d E ⟨X.p, xm⟩ (blk d Y))
    (Nat.beq (Nat.land Y.p Y.m) (nat_lit 0))

@[expose] noncomputable def powLane (d E : Nat) (I X : V) : Nat → V
  | 0 => I
  | e + 1 => mulLane d E (powLane d E I X e) X

@[expose] noncomputable def entK (c : Nat) : Nat :=
  nIf(Nat.blt c (nat_lit 48), nat_lit 0, nIf(Nat.blt c (nat_lit 58), Nat.sub c (nat_lit 48), nat_lit 0))

@[expose] noncomputable def wsK (c : Nat) : Bool :=
  bIf(Nat.beq c (nat_lit 32), true, bIf(Nat.beq c (nat_lit 9), true, bIf(Nat.beq c (nat_lit 10), true,
    bIf(Nat.beq c (nat_lit 13), true, bIf(Nat.beq c (nat_lit 11), true, Nat.beq c (nat_lit 12))))))

@[expose] noncomputable def entOK (L : V) (k e : Nat) : Bool :=
  strictB (Nat.mod e (nat_lit 3)) fun t =>
    bAnd(Bool.rec (motive := fun _ => Bool) (Bool.not (Nat.beq t (nat_lit 1))) (Nat.beq t (nat_lit 1))
        (Nat.testBit L.p k),
      Bool.rec (motive := fun _ => Bool) (Bool.not (Nat.beq t (nat_lit 2))) (Nat.beq t (nat_lit 2))
        (Nat.testBit L.m k))

@[expose] noncomputable def seedBody (N : Nat) (L : V) (cs : List Char) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool)
    (fun k => Nat.ble N k)
    (fun ch _ ih k => strictB (Char.toNat ch) fun c =>
      bIf(wsK c, ih k,
        bIf(Nat.blt k N, bAnd(entOK L k (entK c), ih (Nat.succ k)), ih (Nat.succ k))))
    cs

@[expose] noncomputable def seedHead (N : Nat) (L : V) (cs : List Char) : Bool :=
  List.rec (motive := fun _ => Bool) (Nat.ble N (nat_lit 0))
    (fun ch rest ih => bIf(Nat.beq (Char.toNat ch) (nat_lit 10), seedBody N L rest (nat_lit 0), ih)) cs

@[expose] noncomputable def seedK (d : Nat) (L : V) (cs : List Char) : Bool :=
  seedHead (Nat.mul d d) L cs

end CFSG.KS.F3L

end
