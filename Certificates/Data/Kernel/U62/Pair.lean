module

public import Certificates.Data.Kernel.F4Mat
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.U62P

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def f8 (T k : Nat) : Nat := fld(T, Nat.mul (nat_lit 8) k, nat_lit 255)

@[expose] noncomputable def f16 (T k : Nat) : Nat := fld(T, Nat.mul (nat_lit 16) k, nat_lit 65535)

@[expose] noncomputable def f72 (T k : Nat) : Nat :=
  fld(T, Nat.mul (nat_lit 72) k, nat_lit 4722366482869645213695)

@[expose] noncomputable def LO : Nat := nat_lit 1574122160956548404565

@[expose] noncomputable def LOV : Nat := nat_lit 1365

@[expose] noncomputable def omB (m M : Nat) : Nat :=
  (fun L H => Nat.lor H (Nat.shiftLeft (Nat.xor L H) (nat_lit 1)))
    (Nat.land M m) (Nat.land (Nat.shiftRight M (nat_lit 1)) m)

@[expose] noncomputable def barB (m M : Nat) : Nat :=
  (fun L H => Nat.lor (Nat.xor L H) (Nat.shiftLeft H (nat_lit 1)))
    (Nat.land M m) (Nat.land (Nat.shiftRight M (nat_lit 1)) m)

@[expose] noncomputable def omK (M : Nat) : Nat := omB LO M

@[expose] noncomputable def barK (M : Nat) : Nat := barB LO M

@[expose] noncomputable def omV (v : Nat) : Nat := omB LOV v

@[expose] noncomputable def barV (v : Nat) : Nat := barB LOV v

@[expose] noncomputable def mulK (A B : Nat) : Nat :=
  strictN A fun A => strictN B fun B => strictN (omK B) fun W =>
    orN (nat_lit 6) fun i => Nat.shiftLeft (xorN (nat_lit 6) fun k =>
      Nat.xor (nIf(bit A (Nat.add (Nat.mul (nat_lit 12) i) (Nat.mul (nat_lit 2) k)),
          fld(B, Nat.mul (nat_lit 12) k, nat_lit 4095), nat_lit 0))
        (nIf(bit A (Nat.succ (Nat.add (Nat.mul (nat_lit 12) i) (Nat.mul (nat_lit 2) k))),
          fld(W, Nat.mul (nat_lit 12) k, nat_lit 4095), nat_lit 0)))
      (Nat.mul (nat_lit 12) i)

@[expose] noncomputable def mvK (M x : Nat) : Nat :=
  strictN M fun M => strictN x fun x =>
    orN (nat_lit 6) fun i => Nat.shiftLeft (xorN (nat_lit 6) fun j =>
      fm (ent M i j) (fget x j (nat_lit 2))) (Nat.mul (nat_lit 2) i)

@[expose] noncomputable def invK (M : Nat) : Nat := trn (barK M)

@[expose] noncomputable def commK (A B : Nat) : Nat := mulK (mulK A B) (mulK (invK A) (invK B))

@[expose] noncomputable def eqP (A B : Nat) : Bool :=
  strictB A fun A => strictB B fun B =>
    orB (Nat.beq A B) (strictB (omK B) fun W => orB (Nat.beq A W) (Nat.beq A (omK W)))

@[expose] noncomputable def isScal (M : Nat) : Bool := eqP M ONE

@[expose] noncomputable def eqV (u v : Nat) : Bool :=
  strictB u fun u => strictB v fun v =>
    orB (Nat.beq u v) (strictB (omV v) fun w => orB (Nat.beq u w) (Nat.beq u (omV w)))

@[expose] noncomputable def minK (a b : Nat) : Nat := nIf(Nat.blt a b, a, b)

@[expose] noncomputable def keyK (M : Nat) : Nat :=
  strictN M fun M => strictN (omK M) fun W => minK M (minK W (omK W))

@[expose] noncomputable def tvK (v : Nat) : Nat :=
  strictN v fun v => Nat.xor ONE (orN (nat_lit 36) fun t =>
    Nat.shiftLeft (fm (fget v (Nat.div t (nat_lit 6)) (nat_lit 2))
      (sqC (fget v (Nat.mod t (nat_lit 6)) (nat_lit 2)))) (Nat.mul (nat_lit 2) t))

@[expose] noncomputable def wordK (F : Nat → Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) ONE (fun z _ ih => mulK (F z) ih) w

@[expose] noncomputable def prodK (b : Nat) (F : Nat → Nat) (len : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ONE
    (fun l ih => strictN ih fun a => mulK a (F (Nat.add b l))) len

@[expose] noncomputable def prodRK (b : Nat) (F : Nat → Nat) (len : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ONE
    (fun l ih => strictN ih fun a => mulK (F (Nat.add b l)) a) len

@[expose] noncomputable def powK (x m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ONE (fun _ ih => strictN ih fun a => mulK a x) m

@[expose] noncomputable def anyBlk (b : Nat) (f : Nat → Bool) (len : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun l ih => bIf(f (Nat.add b l), true, ih)) len

@[expose] noncomputable def genAt (TV GV : Nat) (SW : List (List Nat)) (k : Nat) : Bool :=
  Nat.beq (f72 GV k) (wordK (fun z => tvK (fget TV z (nat_lit 12))) (SW.getD k []))

@[expose] noncomputable def repAt (GV RV : Nat) (RW : List (List Nat)) (j : Nat) : Bool :=
  strictB (f72 RV j) fun R =>
    bAnd(Nat.beq R (wordK (f72 GV) (RW.getD j [])),
      bAnd(isScal (mulK R R), notB (isScal R)))

@[expose] noncomputable def treeAt (GV LV PT LB : Nat) (i : Nat) : Bool :=
  bIf(Nat.beq i (nat_lit 0), Nat.beq (f72 LV (nat_lit 0)) ONE,
    strictB (f16 PT i) fun p => strictB (f8 LB i) fun l =>
      bAnd(Nat.blt p i, bAnd(Nat.blt l (nat_lit 13),
        Nat.beq (mulK (f72 LV p) (f72 GV l)) (f72 LV i))))

@[expose] noncomputable def sortAt (LV SO n : Nat) (i : Nat) : Bool :=
  strictB (f16 SO i) fun a => bAnd(Nat.blt a n,
    bIf(Nat.blt (Nat.succ i) n,
      strictB (f16 SO (Nat.succ i)) fun b => bAnd(Nat.blt b n,
        Nat.blt (keyK (f72 LV a)) (keyK (f72 LV b))),
      true))

@[expose] noncomputable def phiAt (LV UP XP NX : Nat) (i : Nat) : Bool :=
  strictB (f72 LV i) fun L => anyN NX fun k => strictB (f16 XP k) fun p =>
    strictB (fget UP p (nat_lit 12)) fun v =>
      andB (Nat.blt p (nat_lit 693)) (notB (eqV (mvK L v) (barV v)))

@[expose] noncomputable def normAt (GV LV NI n : Nat) (k : Nat) : Bool :=
  strictB (f16 NI k) fun i => bAnd(Nat.blt i n, eqP (barK (f72 GV k)) (f72 LV i))

@[expose] noncomputable def fixAt (GV UP : Nat) (q : Nat) : Bool :=
  strictB (fget UP q (nat_lit 12)) fun v =>
    Bool.rec (motive := fun _ => Bool → Bool)
      (fun b => notB b) (fun b => b) (Nat.beq q (nat_lit 0))
      (allN (nat_lit 13) fun k => eqV (mvK (f72 GV k) v) v)

@[expose] noncomputable def scanAt (LV PO EI NO : Nat) (i : Nat) : Bool :=
  strictB (f72 LV i) fun L =>
    bIf(isScal (mulK L (barK L)),
      strictB (f16 PO i) fun q => bAnd(Nat.blt q NO, Nat.beq (f16 EI q) i), true)

@[expose] noncomputable def poolAt (PV : Nat) (p : Nat) : Bool :=
  strictB (f72 PV p) fun P =>
    bAnd(Nat.beq (mulK (trn P) (barK P)) ONE, Nat.beq (det P) (nat_lit 1))

@[expose] noncomputable def recAt (PV NP G1 G2 GG : Nat) (g : Nat) : Bool :=
  strictB (f16 G1 g) fun a => strictB (f16 G2 g) fun b =>
    bAnd(Nat.blt a NP, bAnd(Nat.blt b NP, Nat.beq (f72 GG g) (commK (f72 PV a) (f72 PV b))))

structure WTab where
  PV : Nat
  G1 : Nat
  G2 : Nat
  GG : Nat
  NG : Nat
  GL : Nat
  GT : Nat
  NE : Nat
  NS : Nat
  NC : Nat
  WM : Nat
  WS : Nat
  WC : Nat

@[expose] noncomputable def eltK (R L m : Nat) : Nat := nIf(Nat.beq m (nat_lit 1), R,
  nIf(Nat.beq m (nat_lit 2), L, mulK R L))

@[expose] noncomputable def commE (C T m : Nat) : Bool :=
  bIf(Nat.beq m (nat_lit 1), eqP (mulK C T) (mulK T C), eqP (mulK C T) (mulK T (barK C)))

@[expose] noncomputable def gOK (T : WTab) (R L u : Nat) : Bool :=
  strictB (f16 T.GL u) fun g => strictB (f8 T.GT u) fun m =>
    bAnd(Nat.blt g T.NG, bAnd(Nat.blt (nat_lit 0) m, bAnd(Nat.blt m (nat_lit 4),
      strictB (eltK R L m) fun E =>
        bAnd(bIf(Nat.beq m (nat_lit 1), notB (isScal R), true),
          bAnd(commE (f72 T.PV (f16 T.G1 g)) E m, commE (f72 T.PV (f16 T.G2 g)) E m)))))

@[expose] noncomputable def gamK (T : WTab) (f : Nat) : Nat :=
  prodK (f16 T.NS f) (fun u => f72 T.GG (f16 T.GL u)) (f8 T.NC f)

@[expose] noncomputable def gamIK (T : WTab) (f : Nat) : Nat :=
  prodRK (f16 T.NS f) (fun u => invK (f72 T.GG (f16 T.GL u))) (f8 T.NC f)

@[expose] noncomputable def nVal (T : WTab) (R L f : Nat) : Nat :=
  strictN (f8 T.NE f) fun m => strictN (eltK R L m) fun E =>
  strictN (gamK T f) fun G => strictN (gamIK T f) fun Gi =>
    nIf(Nat.beq m (nat_lit 1), mulK (mulK E G) (mulK E Gi),
      mulK (mulK E (barK G)) (mulK (barK E) Gi))

@[expose] noncomputable def wVal (T : WTab) (R L w : Nat) : Nat :=
  prodK (f16 T.WS w) (nVal T R L) (f8 T.WC w)

@[expose] noncomputable def witAt (T : WTab) (R L w : Nat) : Bool :=
  bAnd(CFSG.KC.Enum.allBlk (f16 T.WS w) (fun f =>
      bAnd(Nat.blt (nat_lit 0) (f8 T.NE f), bAnd(Nat.blt (f8 T.NE f) (nat_lit 4),
        CFSG.KC.Enum.allBlk (f16 T.NS f) (gOK T R L) (f8 T.NC f)))) (f8 T.WC w),
    strictB (powK (wVal T R L w) (f8 T.WM w)) fun z => strictB (mulK z z) fun z2 =>
      bAnd(notB (isScal z2), isScal (mulK z2 z2)))

structure ETab where
  W : WTab
  LV : Nat
  RV : Nat
  EI : Nat
  ES : Nat
  EC : Nat
  WJ : Nat

@[expose] noncomputable def entAt (T : ETab) (q : Nat) : Bool :=
  strictB (f72 T.LV (f16 T.EI q)) fun L =>
    bAnd(isScal (mulK L (barK L)),
      allN (nat_lit 43) fun j => strictB (f72 T.RV j) fun R =>
        bIf(eqP (mulK L (barK R)) (mulK R L),
          anyBlk (f16 T.ES q) (fun w => bAnd(Nat.beq (f8 T.WJ w) j, witAt T.W R L w)) (f8 T.EC q),
          true))

end CFSG.KC.U62P

end
