module

public import Certificates.Data.Kernel.O8.SA

public section

namespace CFSG.KC.O8P

open CFSG.KC.Enum CFSG.KC.O8

@[expose] noncomputable def f1 (T k : Nat) : Nat := fld(T, k, nat_lit 1)

@[expose] noncomputable def f8 (T k : Nat) : Nat := fld(T, Nat.mul (nat_lit 8) k, nat_lit 255)

@[expose] noncomputable def f13 (T k : Nat) : Nat := fld(T, Nat.mul (nat_lit 13) k, nat_lit 8191)

@[expose] noncomputable def f16 (T k : Nat) : Nat := fld(T, Nat.mul (nat_lit 16) k, nat_lit 65535)

@[expose] noncomputable def anyBlk (b : Nat) (f : Nat → Bool) (len : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun l ih => bIf(f (Nat.add b l), true, ih)) len

@[expose] noncomputable def prodK (b : Nat) (F : Nat → Nat) (len : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idK
    (fun l ih => strictN ih fun a => matMulK a (F (Nat.add b l))) len

@[expose] noncomputable def prodRK (b : Nat) (F : Nat → Nat) (len : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idK
    (fun l ih => strictN ih fun a => matMulK (F (Nat.add b l)) a) len

@[expose] noncomputable def powK (x m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idK (fun _ ih => strictN ih fun a => matMulK a x) m

@[expose] noncomputable def slpAt (V A B k : Nat) : Bool :=
  bIf(Nat.blt k (nat_lit 8), true,
    strictB (f16 A k) fun a => strictB (f16 B k) fun b =>
      bAnd(Nat.blt a k, bAnd(Nat.blt b k,
        Nat.beq (matMulK (saAtK V a) (saAtK V b)) (saAtK V k))))

@[expose] noncomputable def chiAt (PT LT CH i : Nat) : Bool :=
  bIf(Nat.beq i (nat_lit 0), Nat.beq (f1 CH (nat_lit 0)) (nat_lit 0),
    Nat.beq (f1 CH i) (Nat.xor (f1 CH (ix13 PT i))
      (nIf(Nat.beq (fld(LT, Nat.mul (nat_lit 3) i, nat_lit 7)) (nat_lit 4), nat_lit 1, nat_lit 0))))

@[expose] noncomputable def scanAt (SC CH PO EI NO i : Nat) : Bool :=
  strictB (saAtK SC i) fun x =>
  bIf(bAnd(bIf(Nat.beq i (nat_lit 0), false, true),
      bAnd(Nat.beq (matMulK x x) idK, Nat.beq (f1 CH i) (nat_lit 1))),
    strictB (f8 PO i) fun q => bAnd(Nat.blt q NO, Nat.beq (f13 EI q) i), true)

@[expose] noncomputable def maskK (y x m : Nat) : Nat :=
  matMulK (nIf(Nat.beq (f1 m (nat_lit 0)) (nat_lit 1), y, idK))
    (nIf(Nat.beq (f1 m (nat_lit 1)) (nat_lit 1), x, idK))

structure GTab where
  V : Nat
  NR : Nat
  GT : Nat
  G1 : Nat
  G1I : Nat
  G2 : Nat
  G2I : Nat

@[expose] noncomputable def gOK (T : GTab) (y x g : Nat) : Bool :=
  strictB (maskK y x (f8 T.GT g)) fun t =>
  strictB (f16 T.G1 g) fun a => strictB (f16 T.G1I g) fun ai =>
  strictB (f16 T.G2 g) fun b => strictB (f16 T.G2I g) fun bi =>
  strictB (saAtK T.V a) fun A => strictB (saAtK T.V b) fun B =>
    bAnd(bIf(Nat.beq t idK, false, true),
    bAnd(Nat.blt a T.NR, bAnd(Nat.blt ai T.NR, bAnd(Nat.blt b T.NR, bAnd(Nat.blt bi T.NR,
    bAnd(Nat.beq (matMulK A (saAtK T.V ai)) idK, bAnd(Nat.beq (matMulK B (saAtK T.V bi)) idK,
    bAnd(Nat.beq (matMulK A t) (matMulK t A), Nat.beq (matMulK B t) (matMulK t B)))))))))

@[expose] noncomputable def gVal (T : GTab) (g : Nat) : Nat :=
  matMulK (matMulK (saAtK T.V (f16 T.G1 g)) (saAtK T.V (f16 T.G2 g)))
    (matMulK (saAtK T.V (f16 T.G1I g)) (saAtK T.V (f16 T.G2I g)))

@[expose] noncomputable def gInv (T : GTab) (g : Nat) : Nat :=
  matMulK (matMulK (saAtK T.V (f16 T.G2 g)) (saAtK T.V (f16 T.G1 g)))
    (matMulK (saAtK T.V (f16 T.G2I g)) (saAtK T.V (f16 T.G1I g)))

structure WTab where
  G : GTab
  NE : Nat
  NS : Nat
  NC : Nat
  WM : Nat
  WS : Nat
  WC : Nat

@[expose] noncomputable def nVal (T : WTab) (y x f : Nat) : Nat :=
  strictN (maskK y x (f8 T.NE f)) fun e =>
  strictN (prodK (f16 T.NS f) (gVal T.G) (f8 T.NC f)) fun c =>
  strictN (prodRK (f16 T.NS f) (gInv T.G) (f8 T.NC f)) fun ci =>
    matMulK (matMulK e c) (matMulK e ci)

@[expose] noncomputable def wVal (T : WTab) (y x w : Nat) : Nat :=
  prodK (f16 T.WS w) (nVal T y x) (f8 T.WC w)

@[expose] noncomputable def witAt (T : WTab) (y x w : Nat) : Bool :=
  bAnd(allBlk (f16 T.WS w) (fun f => allBlk (f16 T.NS f) (gOK T.G y x) (f8 T.NC f)) (f8 T.WC w),
    strictB (powK (wVal T y x w) (f8 T.WM w)) fun z => strictB (matMulK z z) fun z2 =>
      bAnd(bIf(Nat.beq z2 idK, false, true), Nat.beq (matMulK z2 z2) idK))

structure ETab where
  W : WTab
  SC : Nat
  YI : Nat
  IN : Nat
  EI : Nat
  ES : Nat
  EC : Nat
  WJ : Nat

@[expose] noncomputable def entAt (T : ETab) (q : Nat) : Bool :=
  strictB (saAtK T.SC (f13 T.EI q)) fun x =>
  allN (nat_lit 38) fun j => bIf(Nat.beq (f1 T.IN j) (nat_lit 1),
    strictB (saAtK T.SC (ix13 T.YI j)) fun y =>
      bIf(Nat.beq (matMulK x y) (matMulK y x),
        anyBlk (f16 T.ES q) (fun w => bAnd(Nat.beq (f8 T.WJ w) j, witAt T.W y x w)) (f8 T.EC q),
        true),
    true)

end CFSG.KC.O8P

end
