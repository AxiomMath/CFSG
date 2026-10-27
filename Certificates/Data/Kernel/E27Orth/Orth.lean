module

public import Certificates.Data.Kernel.E27Orth.Defs
public import Certificates.Data.Kernel.Misc.G24

public section

namespace CFSG.KC.E27Orth

open CFSG.KC.Enum CFSG.KC.Misc.G24

@[expose] noncomputable def colF2 (n X j : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add acc (Nat.mul (bit X (Nat.add (Nat.mul n i) j)) (Nat.pow (nat_lit 2) i))) n

@[expose] noncomputable def trF2 (n X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Nat.add acc (Nat.mul (colF2 n X j) (Nat.pow (nat_lit 2) (Nat.mul n j)))) n

@[expose] noncomputable def qOK (n U X : Nat) : Bool :=
  strictB (Nat.xor (mulF2 n (mulF2 n (trF2 n X) U) X) U) fun M =>
    bAnd(Nat.beq (Nat.land M (oneF2 n)) (nat_lit 0), Nat.beq (trF2 n M) M)

@[expose] noncomputable def orthI (n U X Xi : Nat) : Bool :=
  strictB (oneF2 n) fun one => bAnd(Nat.beq (mulF2 n X Xi) one,
    bAnd(Nat.beq (mulF2 n Xi X) one, qOK n U X))

@[expose] noncomputable def omI (n U x y yi : Nat) : Bool :=
  strictB (mulF2 n x x) fun x2 => strictB (mulF2 n x2 x2) fun x4 => strictB (mulF2 n x4 x4) fun x8 =>
    bAnd(orthI n U x x8, bAnd(orthI n U y yi, Nat.beq (mulF2 n y x) (mulF2 n x8 y)))

@[expose] noncomputable def spreadF2 (n k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add acc (Nat.mul (bit k i) (Nat.pow (nat_lit 2) (Nat.mul n i)))) n

@[expose] noncomputable def fixK (n X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.add acc (nIf(Nat.beq (colF2 n (mulF2 n X (spreadF2 n k)) (nat_lit 0)) k,
      nat_lit 1, nat_lit 0))) (Nat.pow (nat_lit 2) n)

@[expose] noncomputable def cenI (n one m c0 : Nat) (G E : Nat → Nat) (i : Nat) : Bool :=
  strictB (E i) fun x => bAnd(allN m fun j => bAnd(cnF2 n (mulF2 n (G j) x),
      cnF2 n (mulF2 n x (G j))),
    bIf(allBlk (nat_lit 0) (fun j => Nat.beq (mulF2 n (G j) x) (mulF2 n x (G j))) m,
      bIf(Nat.beq x one, true, Nat.beq (fixK n x) c0), true))

@[expose] noncomputable def fsI (n one c0 nF : Nat) (E F Fm : Nat → Nat) (i : Nat) : Bool :=
  strictB (Fm i) fun f => bIf(Nat.beq f (nat_lit 0),
    strictB (E i) fun x => bIf(Nat.beq x one, true, strictB (mulF2 n x x) fun x2 =>
      strictB (mulF2 n x x2) fun y => bIf(Nat.beq y one, bIf(Nat.beq (fixK n x) c0, false, true),
        bAnd(cnF2 n x2, cnF2 n y))),
    bAnd(Nat.blt (Nat.pred f) nF, Nat.beq (F (Nat.pred f)) i))

@[expose] noncomputable def pw3 (n one a i : Nat) : Nat :=
  nIf(Nat.beq i (nat_lit 0), one, nIf(Nat.beq i (nat_lit 1), a, mulF2 n a a))

@[expose] noncomputable def pairI (n one c0 nF : Nat) (E F Pw : Nat → Nat) (q : Nat) : Bool :=
  strictB (E (F (Nat.div q nF))) fun a => strictB (E (F (Nat.mod q nF))) fun b =>
    strictB (mulF2 n a b) fun ab => strictB (mulF2 n b a) fun ba =>
    bIf(Nat.beq ab ba,
      bIf(Nat.beq b one, true, bIf(Nat.beq b a, true, bIf(Nat.beq b (mulF2 n a a), true,
        strictB (Pw q) fun w =>
          strictB (mulF2 n (pw3 n one a (Nat.div w (nat_lit 3)))
            (pw3 n one b (Nat.mod w (nat_lit 3)))) fun p =>
          bAnd(cnF2 n p, bAnd(bIf(Nat.beq p one, false, true),
            bIf(Nat.beq (fixK n p) c0, false, true)))))),
      bAnd(cnF2 n ab, cnF2 n ba))

@[expose] noncomputable def coverI (n one NB nW : Nat) (E EB Wg Cv : Nat → Nat) (i : Nat) :
    Bool :=
  strictB (E i) fun x => bIf(Nat.beq x one, true, strictB (mulF2 n x x) fun x2 =>
    strictB (mulF2 n x x2) fun y => bIf(Nat.beq y one,
      strictB (Cv i) fun t => strictB (Nat.shiftRight t (nat_lit 16)) fun w =>
        strictB (Nat.land t (nat_lit 65535)) fun b => bAnd(Nat.blt w nW, bAnd(Nat.blt b NB,
          Nat.beq (mulF2 n (Wg w) x) (mulF2 n (EB b) (Wg w)))),
      bAnd(cnF2 n x2, cnF2 n y)))

@[expose] noncomputable def commI (n m : Nat) (G : Nat → Nat) (q : Nat) : Bool :=
  strictB (G (Nat.div q m)) fun a => strictB (G (Nat.mod q m)) fun b =>
    Nat.beq (mulF2 n a b) (mulF2 n b a)

end CFSG.KC.E27Orth

end
