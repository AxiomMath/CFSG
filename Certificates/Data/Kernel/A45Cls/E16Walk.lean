module

public import Certificates.Data.Kernel.A45Cls.Defs

public section

namespace CFSG.KC.E16Walk

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.KC.BfsPin

@[expose] noncomputable def M64 : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 64)) (nat_lit 1)

@[expose] noncomputable def bitK (m i : Nat) : Bool :=
  Nat.blt (nat_lit 0) (Nat.land m (Nat.shiftLeft (nat_lit 1) i))

@[expose] noncomputable def notK (a : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false a

@[expose] noncomputable def bEqK (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (notK b) b a

@[expose] noncomputable def jK (e : Nat) : Nat := Nat.land e (nat_lit 255)

@[expose] noncomputable def posK (e : Nat) : Nat := fld(e, nat_lit 8, nat_lit 255)

@[expose] noncomputable def rowK (e : Nat) : Nat := Nat.shiftRight e (nat_lit 16)

@[expose] noncomputable def mK (q : Nat) : Nat := Nat.land q M64

@[expose] noncomputable def pmK (q : Nat) : Nat := fld(q, nat_lit 64, M64)

@[expose] noncomputable def dK (q : Nat) : Nat := Nat.shiftRight q (nat_lit 128)

@[expose] noncomputable def popK (m : Nat) : Nat := cntN (nat_lit 64) fun i => bitK m i

@[expose] noncomputable def subK (c u : Nat) : Bool := Nat.beq (Nat.land c u) c

@[expose] noncomputable def orBits (f : Nat → Nat) (E : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun e _ ih => Nat.lor (Nat.shiftLeft (nat_lit 1) (f e)) ih) E

@[expose] noncomputable def invOK (T : Nat → Nat) (N im : Nat) : Bool :=
  allN N fun i => bEqK (isInvK 45 6 (T i)) (bitK im i)

@[expose] noncomputable def tabOK (im n posT jT : Nat) (E : List Nat) : Bool :=
  bAnd(Nat.beq (orBits jK E) im, bAnd(Nat.beq (orBits posK E)
      (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1)),
    List.rec (motive := fun _ => Bool) true (fun e _ ih =>
      bAnd(Nat.beq fld(posT, Nat.mul (nat_lit 6) (jK e), nat_lit 63) (posK e),
        bAnd(Nat.beq fld(jT, Nat.mul (nat_lit 8) (posK e), nat_lit 255) (jK e), ih))) E))

@[expose] noncomputable def posOK (N im posT jT : Nat) : Bool :=
  allN N fun j => Bool.rec (motive := fun _ => Bool)
    (Nat.beq fld(posT, Nat.mul (nat_lit 6) j, nat_lit 63) (nat_lit 63))
    (Nat.beq fld(jT, Nat.mul (nat_lit 8) fld(posT, Nat.mul (nat_lit 6) j, nat_lit 63), nat_lit 255) j)
    (bitK im j)

@[expose] noncomputable def adjOK (T : Nat → Nat) (E : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih => bAnd(
    List.rec (motive := fun _ => Bool) true (fun f _ ih2 => bAnd(
      Bool.rec (motive := fun _ => Bool)
        (notK (eq22 45 6 (mask 6) (T (jK e)) (T (jK f)) (T (jK f)) (T (jK e)))) true
        (bitK (rowK e) (posK f)), ih2)) E, ih)) E

@[expose] noncomputable def prodIn (ps : List Nat) (T S : Nat → Nat) (N posT m a b : Nat) : Bool :=
  strictB (findK 45 6 ps T S
      (pkeyK 45 6 ps (pcomp 45 6 (mask 6) (T a) (T b))) (nat_lit 24)
      (nat_lit 0) N) fun j =>
    bAnd(Nat.blt j N, bAnd(Nat.beq (T j) (pcomp 45 6 (mask 6) (T a) (T b)),
      bitK m fld(posT, Nat.mul (nat_lit 6) j, nat_lit 63)))

@[expose] noncomputable def nodeOK (ps : List Nat) (T S : Nat → Nat) (N posT jT : Nat)
    (E : List Nat) (q : Nat) : Bool :=
  bAnd(Nat.beq (popK (mK q)) (Nat.succ (Nat.mul (nat_lit 2) (popK (pmK q)))),
  bAnd(bitK (mK q) (dK q), bAnd(notK (bitK (pmK q) (dK q)), bAnd(subK (pmK q) (mK q),
    List.rec (motive := fun _ => Bool) true (fun f _ ih => bAnd(
      Bool.rec (motive := fun _ => Bool) true
        (prodIn ps T S N posT (mK q) fld(jT, Nat.mul (nat_lit 8) (dK q), nat_lit 255) (jK f))
        (bitK (pmK q) (posK f)), ih)) E))))

@[expose] noncomputable def nodesOK (ps : List Nat) (T S : Nat → Nat) (N posT jT : Nat)
    (E Q : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun q _ ih => bAnd(nodeOK ps T S N posT jT E q, ih)) Q

@[expose] noncomputable def inMasks (P : List Nat) (x : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun p _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq (mK p) x)) P

@[expose] noncomputable def par1OK (full : Nat) (Q : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun q _ ih => bAnd(subK (mK q) full, bAnd(Nat.beq (popK (pmK q)) (nat_lit 1), ih))) Q

@[expose] noncomputable def parOK (full : Nat) (P Q : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun q _ ih => bAnd(subK (mK q) full, bAnd(inMasks P (pmK q), ih))) Q

@[expose] noncomputable def candK (full : Nat) (E : List Nat) (p : Nat) : Nat :=
  (fun c => Nat.sub c (Nat.land c p))
    (List.rec (motive := fun _ => Nat) full
      (fun e _ ih => nIf(bitK p (posK e), Nat.land (rowK e) ih, ih)) E)

@[expose] noncomputable def unionK (Q : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun q _ ih => nIf(Nat.beq (Nat.land (mK q) p) p, Nat.lor (mK q) ih, ih)) Q

@[expose] noncomputable def complK (full : Nat) (E P Q : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => bAnd(subK (candK full E (mK p)) (unionK Q (mK p)), ih)) P

@[expose] noncomputable def compl1K (full : Nat) (E Q : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih => bAnd(subK (candK full E (Nat.shiftLeft (nat_lit 1) (posK e)))
      (unionK Q (Nat.shiftLeft (nat_lit 1) (posK e))), ih)) E

@[expose] noncomputable def fixOK (T : Nat → Nat) (F15 FP : Nat) (E : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih => bAnd(bAnd(
    bEqK (bitK F15 (posK e)) (Nat.beq (fixK 45 6 (T (jK e))) (nat_lit 15)),
    bEqK (bitK FP (posK e)) (Bool.rec (motive := fun _ => Bool)
      (Nat.beq (fixK 45 6 (T (jK e))) (nat_lit 5)) true
      (Nat.beq (fixK 45 6 (T (jK e))) (nat_lit 13)))), ih)) E

@[expose] noncomputable def goodK (F15 FP : Nat) (Q : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun q _ ih => bAnd(bAnd(
    Bool.rec (motive := fun _ => Bool) (notK (Nat.beq (Nat.land (mK q) F15) (nat_lit 0))) true
      (subK (mK q) FP),
    Nat.ble (popK (Nat.land (mK q) F15)) (nat_lit 4)), ih)) Q

end CFSG.KC.E16Walk
