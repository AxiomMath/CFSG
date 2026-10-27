module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.N3153

open CFSG.KC.Enum

@[expose] noncomputable def rg (r i : Nat) : Nat := fld(r, Nat.mul (nat_lit 16) i, nat_lit 65535)

@[expose] def decodeRow (d r : Nat) : List Nat :=
  (List.range d).map fun i => (r >>> (16 * i)) &&& 65535

@[expose] def rowsArr (n d : Nat) (R : Nat → Nat) : Array (List Nat) :=
  Array.ofFn (n := n) fun x => decodeRow d (R x.val)

@[expose] noncomputable def maskK (d r : Nat) : Nat :=
  foldN d (fun i a => Nat.add (Nat.lor a (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 64) (rg r i))))
    (nat_lit 1)) (nat_lit 0)

@[expose] noncomputable def spreadK (d r : Nat) : Nat :=
  foldN d (fun i a => Nat.add (Nat.add a (Nat.shiftLeft (nat_lit 1)
    (Nat.add (nat_lit 128) (Nat.mul (nat_lit 48) (rg r i))))) (nat_lit 1)) (nat_lit 0)

@[expose] noncomputable def rowOK (n d : Nat) (R M S : Nat → Nat) (x : Nat) : Bool :=
  strictB (R x) fun r =>
    bAnd(Nat.blt (rg r (Nat.sub d (nat_lit 1))) n,
    bAnd(allN (Nat.sub d (nat_lit 1)) (fun i => Nat.blt (rg r i) (rg r (Nat.add i (nat_lit 1)))),
    bAnd(Nat.beq (Nat.shiftRight (maskK d r) (nat_lit 64)) (M x),
      Nat.beq (Nat.add (spreadK d r) (Nat.add x (nat_lit 1))) (Nat.add (S x) d))))

@[expose] noncomputable def imgMaskK (d g r : Nat) : Nat :=
  foldN d (fun i a => Nat.add (Nat.lor a (Nat.shiftLeft (nat_lit 1)
    (Nat.add (nat_lit 64) (pg (nat_lit 12) (nat_lit 4095) g (rg r i))))) (nat_lit 1)) (nat_lit 0)

@[expose] noncomputable def imgOK (n d g : Nat) (R M : Nat → Nat) (x : Nat) : Bool :=
  strictB (pg (nat_lit 12) (nat_lit 4095) g x) fun y =>
    bAnd(Nat.blt y n, strictB (R x) fun r =>
      Nat.beq (Nat.shiftRight (imgMaskK d g r) (nat_lit 64)) (M y))

@[expose] noncomputable def treeOK (n ng : Nat) (G T : Nat → Nat) (x : Nat) : Bool :=
  bIf(Nat.beq x (nat_lit 0), true, strictB (T x) fun e => strictB (fld(e, nat_lit 0, nat_lit 65535))
    fun p => bAnd(Nat.blt p n, bAnd(Nat.blt (fld(e, nat_lit 16, nat_lit 255)) ng,
      bAnd(Nat.blt (fld(T p, nat_lit 24, nat_lit 65535)) (fld(e, nat_lit 24, nat_lit 65535)),
        Nat.beq (pg (nat_lit 12) (nat_lit 4095) (G (fld(e, nat_lit 16, nat_lit 255))) p) x))))

@[expose] noncomputable def rootOK (M : Nat → Nat) (Z i : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (bIf(Nat.beq i (nat_lit 0), true, Bool.not (Nat.beq (pg (nat_lit 12) (nat_lit 4095) Z i) i)))
    (bAnd(Bool.not (Nat.beq i (nat_lit 0)), Nat.beq (pg (nat_lit 12) (nat_lit 4095) Z i) i))
    (Nat.beq (fld(M (nat_lit 0), i, nat_lit 1)) (nat_lit 1))

@[expose] noncomputable def sym0OK (R M : Nat → Nat) (i : Nat) : Bool :=
  Nat.beq (Nat.land (M (rg (R (nat_lit 0)) i)) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def cget (C v : Nat) : Nat :=
  fld(C, Nat.add (nat_lit 64) (Nat.mul (nat_lit 32) v), nat_lit 4294967295)

@[expose] noncomputable def hcK (x : Nat) : Nat :=
  strictN (Nat.mod (Nat.add (Nat.mul (Nat.mod x (nat_lit 2147483629)) (nat_lit 1000003))
    (nat_lit 12345)) (nat_lit 2147483629)) fun y =>
  strictN (Nat.mod (Nat.add (Nat.mul y y) (nat_lit 7919)) (nat_lit 2147483629)) fun y =>
  Nat.mod (Nat.add (Nat.mul y y) (nat_lit 104729)) (nat_lit 2147483629)

@[expose] noncomputable def idxK (pre : List Nat) (v : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun a _ ih =>
    nIf(Nat.beq a v, nat_lit 1, nIf(Nat.beq ih (nat_lit 0), nat_lit 0, Nat.add ih (nat_lit 1))))
    pre

@[expose] noncomputable def initVal (T : Nat) (pre : List Nat) (v : Nat) : Nat :=
  Nat.add (Nat.mul (nat_lit 2) (idxK pre v))
    (nIf(Nat.beq (pg (nat_lit 12) (nat_lit 4095) T v) v, nat_lit 1, nat_lit 0))

@[expose] noncomputable def initK (n T : Nat) (pre : List Nat) : Nat :=
  foldN n (fun v a => Nat.add (Nat.add a (Nat.shiftLeft (initVal T pre v)
    (Nat.add (nat_lit 64) (Nat.mul (nat_lit 32) v)))) (nat_lit 1)) (nat_lit 0)

@[expose] noncomputable def accK (n : Nat) (S : Nat → Nat) (C : Nat) : Nat :=
  foldN n (fun w a => Nat.add a (Nat.mul (hcK (cget C w)) (S w))) (nat_lit 0)

@[expose] noncomputable def newCol (T C A v : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.mul (Nat.mod (Nat.add
    (Nat.mul (Nat.mod (cget C v) (nat_lit 2147483629)) (nat_lit 1000003))
    (Nat.mod (cget C (pg (nat_lit 12) (nat_lit 4095) T v)) (nat_lit 2147483629)))
    (nat_lit 2147483629)) (nat_lit 1000003))
    fld(A, Nat.add (nat_lit 128) (Nat.mul (nat_lit 48) v), nat_lit 281474976710655))
    (nat_lit 2147483629)

@[expose] noncomputable def stepK (n : Nat) (S : Nat → Nat) (T C : Nat) : Nat :=
  strictN (accK n S C) fun A => foldN n (fun v a => Nat.add (Nat.add a (Nat.shiftLeft
    (newCol T C A v) (Nat.add (nat_lit 64) (Nat.mul (nat_lit 32) v)))) (nat_lit 1)) (nat_lit 0)

@[expose] noncomputable def colourK (n : Nat) (S : Nat → Nat) (T : Nat) (pre : List Nat)
    (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (initK n T pre)
    (fun _ C => strictN C fun C => stepK n S T C) k

@[expose] noncomputable def cellCnt (n C col : Nat) : Nat :=
  foldN n (fun w a => nIf(Nat.beq (cget C w) col, Nat.add a (nat_lit 1), a)) (nat_lit 0)

@[expose] noncomputable def cellK (n : Nat) (S : Nat → Nat) (T : Nat) (pts : List Nat)
    (k s b : Nat) : Bool :=
  strictB (colourK n S T (pts.take s) k) fun C =>
    Nat.beq (cellCnt n C (cget C (pts.getD s (nat_lit 0)))) b

@[expose] noncomputable def injK (n : Nat) (S : Nat → Nat) (T : Nat) (pts : List Nat) (k P : Nat) :
    Bool :=
  strictB (colourK n S T pts k) fun C =>
    bAnd(allN n (fun i => Nat.blt (rg P i) n),
      allN (Nat.sub n (nat_lit 1)) (fun i =>
        Nat.blt (cget C (rg P i)) (cget C (rg P (Nat.add i (nat_lit 1))))))

end CFSG.KC.N3153

end
