module

public import Certificates.Data.Kernel.Fi22Nbr3153
public import Certificates.Data.CFSGNative.FischerOddCore.Checks

public section

namespace CFSG.KC.S2071

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.Sporadic.FischerOddCore.Native

@[expose] noncomputable def wd (D j : Nat) : Nat :=
  fld(D, Nat.mul (nat_lit 64) j, nat_lit 18446744073709551615)

@[expose] noncomputable def allL (l : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => bAnd(f a, ih)) l

@[expose] noncomputable def lenL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.add ih (nat_lit 1)) l

@[expose] noncomputable def getL (l : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun a _ ih i => nIf(Nat.beq i (nat_lit 0), a, ih (Nat.sub i (nat_lit 1)))) l

@[expose] noncomputable def memL (l : List Nat) (x : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => bIf(Nat.beq a x, true, ih)) l

@[expose] noncomputable def eqL (l : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun m => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) m)
    (fun a _ ih m => List.rec (motive := fun _ => Bool) false
      (fun b m' _ => bAnd(Nat.beq a b, ih m')) m) l

@[expose] noncomputable def kidsOK (nodes : Array SNode) (N : SNode) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun rk _ ih =>
    bAnd(Nat.blt rk.2 nodes.size, bAnd(eqL (nodes[rk.2]!).pre (N.pre ++ [rk.1]), ih))) N.kids

@[expose] noncomputable def repsL (N : SNode) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun rk _ ih => rk.1 :: ih) N.kids

@[expose] noncomputable def recStep (n : Nat) (PL : Nat → Nat) (N : SNode) (e s : Nat) : Nat :=
  strictN (fld(e, nat_lit 0, nat_lit 65535)) fun w =>
  strictN (fld(e, nat_lit 16, nat_lit 65535)) fun p =>
  strictN (fld(e, nat_lit 32, nat_lit 65535)) fun g =>
    Nat.add (Nat.lor (Nat.sub s (Nat.land s (nat_lit 1)))
        (Nat.shiftLeft (nat_lit 1) (Nat.add w (nat_lit 1))))
      (nIf(Nat.beq (Nat.land s (nat_lit 1)) (nat_lit 1),
        nIf(Nat.blt w n,
          nIf(Nat.beq (fld(e, nat_lit 48, nat_lit 1)) (nat_lit 1),
            nIf(memL (repsL N) w, nat_lit 1, nat_lit 0),
            nIf(Nat.beq (fld(s, Nat.add p (nat_lit 1), nat_lit 1)) (nat_lit 1),
              nIf(Nat.blt g (lenL N.pool),
                nIf(Nat.beq (pg (nat_lit 12) (nat_lit 4095) (PL (getL N.pool g)) p) w,
                  nat_lit 1, nat_lit 0), nat_lit 0), nat_lit 0)), nat_lit 0), nat_lit 0))

@[expose] noncomputable def recMask (n : Nat) (PL : Nat → Nat) (N : SNode) (D : Nat) : Nat :=
  strictN (wd D (nat_lit 0)) fun m =>
    foldN m (fun i s => recStep n PL N (wd D (Nat.sub m i)) s) (nat_lit 1)

@[expose] noncomputable def branchK (n : Nat) (S : Nat → Nat) (T : Nat) (PL : Nat → Nat)
    (np : Nat) (nodes : Array SNode) (k col D : Nat) (N : SNode) : Bool :=
  bAnd(Nat.beq N.out (nat_lit 0),
  bAnd(allL N.pool (fun j => Nat.blt j np),
  bAnd(allL N.pool (fun j => allL N.pre (fun x => Nat.beq (pg (nat_lit 12) (nat_lit 4095) (PL j) x) x)),
  bAnd(kidsOK nodes N,
  strictB (recMask n PL N D) fun s => bAnd(Nat.beq (Nat.land s (nat_lit 1)) (nat_lit 1),
    strictB (colourK n S T N.pre k) fun C =>
      allN n (fun w => bIf(Nat.beq (cget C w) col,
        Nat.beq (fld(s, Nat.add w (nat_lit 1), nat_lit 1)) (nat_lit 1), true)))))))

@[expose] noncomputable def leafK (n : Nat) (S : Nat → Nat) (T : Nat) (AC : Nat → Nat) (na : Nat)
    (base : List Nat) (k D : Nat) (N : SNode) : Bool :=
  strictB (colourK n S T N.pre k) fun C => strictB (colourK n S T base k) fun Cs =>
    bIf(Nat.beq N.out (nat_lit 1),
      bAnd(Nat.blt N.acc na, strictB (AC N.acc) fun A => allN n (fun v =>
        strictB (pg (nat_lit 12) (nat_lit 4095) A v) fun a =>
          bAnd(Nat.blt a n, Nat.beq (cget C a) (cget Cs v)))),
      bAnd(Nat.beq N.out (nat_lit 2), strictB (wd D (nat_lit 1)) fun v =>
        bAnd(Nat.blt v n, strictB (cget Cs v) fun sv =>
          allN n (fun w => Bool.not (Nat.beq (cget C w) sv)))))

@[expose] noncomputable def nodeK (n : Nat) (S : Nat → Nat) (T : Nat) (PL : Nat → Nat) (np : Nat)
    (AC : Nat → Nat) (na : Nat) (nodes : Array SNode) (base SC : List Nat) (k : Nat)
    (DT : Nat → Nat) (i : Nat) : Bool :=
  bIf(Nat.blt (lenL (nodes[i]!).pre) (lenL base),
    branchK n S T PL np nodes k (getL SC (lenL (nodes[i]!).pre)) (DT i) (nodes[i]!),
    leafK n S T AC na base k (DT i) (nodes[i]!))

@[expose] noncomputable def srcColK (n : Nat) (S : Nat → Nat) (T : Nat) (base : List Nat)
    (k d sc : Nat) : Bool :=
  Nat.beq (cget (colourK n S T (base.take d) k) (base.getD d (nat_lit 0))) sc

end CFSG.KC.S2071

end
