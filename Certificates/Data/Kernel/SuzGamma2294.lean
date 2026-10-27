module

public import Certificates.Data.Kernel.Fi22Nbr3153

public section

namespace CFSG.KC.G2294

open CFSG.KC.Enum CFSG.KC.N3153

@[expose] noncomputable def cs (C v : Nat) : Nat :=
  fld(C, Nat.mul (nat_lit 48) v, nat_lit 4294967295)

@[expose] noncomputable def gp (G x : Nat) : Nat := fld(G, Nat.mul (nat_lit 15) x, nat_lit 32767)

@[expose] noncomputable def rowOK (n d : Nat) (R : Nat → Nat) (x : Nat) : Bool :=
  strictB (R x) fun r =>
    bAnd(Nat.blt (rg r (Nat.sub d (nat_lit 1))) n,
      allN (Nat.sub d (nat_lit 1)) (fun i => Nat.blt (rg r i) (rg r (Nat.add i (nat_lit 1)))))

@[expose] noncomputable def imgMask (d G r s : Nat) : Nat :=
  foldN d (fun i a => Nat.add (Nat.lor a (Nat.shiftLeft (nat_lit 1)
    (Nat.add (nat_lit 64) (gp G (rg r i))))) (nat_lit 1)) s

@[expose] noncomputable def rowMask (d r s : Nat) : Nat :=
  foldN d (fun i a => Nat.add (Nat.lor a (Nat.shiftLeft (nat_lit 1)
    (Nat.add (nat_lit 64) (rg r i)))) (nat_lit 1)) s

@[expose] noncomputable def imgOK (n d G : Nat) (R : Nat → Nat) (x : Nat) : Bool :=
  strictB (gp G x) fun y => bAnd(Nat.blt y n,
    strictB (R x) fun r => strictB (R y) fun ry =>
      Nat.beq (Nat.shiftRight (imgMask d G r (Nat.shiftLeft x (nat_lit 16))) (nat_lit 64))
        (Nat.shiftRight (rowMask d ry (Nat.shiftLeft y (nat_lit 16))) (nat_lit 64)))

@[expose] noncomputable def treeOK (n ng : Nat) (G T : Nat → Nat) (x : Nat) : Bool :=
  bIf(Nat.beq x (nat_lit 0), true, strictB (T x) fun e => strictB (fld(e, nat_lit 0, nat_lit 65535))
    fun p => bAnd(Nat.blt p n, bAnd(Nat.blt (fld(e, nat_lit 16, nat_lit 255)) ng,
      bAnd(Nat.blt (fld(T p, nat_lit 24, nat_lit 65535)) (fld(e, nat_lit 24, nat_lit 65535)),
        Nat.beq (gp (G (fld(e, nat_lit 16, nat_lit 255))) p) x))))

@[expose] noncomputable def sym0OK (R : Nat → Nat) (i : Nat) : Bool :=
  Nat.beq (rg (R (rg (R (nat_lit 0)) i)) (nat_lit 0)) (nat_lit 0)

@[expose] noncomputable def cmK : Nat := nat_lit 2147483629

@[expose] noncomputable def initOK (C v : Nat) : Bool :=
  Nat.beq (cs C v) (nIf(Nat.beq v (nat_lit 0), nat_lit 3, nat_lit 1))

@[expose] noncomputable def hashOK (C H v : Nat) : Bool := Nat.beq (cs H v) (hcK (cs C v))

@[expose] noncomputable def hsum (d H r : Nat) : Nat :=
  foldN d (fun i a => Nat.add a (cs H (rg r i))) (nat_lit 0)

@[expose] noncomputable def stepCol (c s : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.mul (Nat.mod (Nat.add (Nat.mul (Nat.mod c cmK) (nat_lit 1000003))
    (Nat.mod c cmK)) cmK) (nat_lit 1000003)) s) cmK

@[expose] noncomputable def roundOK (d : Nat) (R : Nat → Nat) (C H C' v : Nat) : Bool :=
  strictB (R v) fun r => Nat.beq (cs C' v) (stepCol (cs C v) (hsum d H r))

@[expose] noncomputable def baseOK (U : Nat → Nat) (C E C' v : Nat) : Bool :=
  Nat.beq (cs C' v) (Nat.mod (Nat.add (Nat.mul (Nat.mod (cs C v) cmK) (nat_lit 1000003))
    (cs E (U v))) cmK)

@[expose] noncomputable def cellCnt (n C col : Nat) : Nat :=
  foldN n (fun w a => nIf(Nat.beq (cs C w) col, Nat.add a (nat_lit 1), a)) (nat_lit 0)

@[expose] noncomputable def injK (n C P : Nat) : Bool :=
  bAnd(allN n (fun i => Nat.blt (rg P i) n),
    allN (Nat.sub n (nat_lit 1)) (fun i =>
      Nat.blt (cs C (rg P i)) (cs C (rg P (Nat.add i (nat_lit 1))))))

end CFSG.KC.G2294

end
