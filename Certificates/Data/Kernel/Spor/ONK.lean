module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KS.ON

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def vP (X : Nat) : Nat := Nat.land X (mask (nat_lit 256))

@[expose] noncomputable def vM (X : Nat) : Nat := Nat.shiftRight X (nat_lit 256)

@[expose] noncomputable def vmk (p m : Nat) : Nat := Nat.lor p (Nat.shiftLeft m (nat_lit 256))

@[expose] noncomputable def addP (ap am bp bm : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.xor ap (Nat.land ap (Nat.lor bp bm))) (Nat.xor bp (Nat.land bp (Nat.lor ap am))))
    (Nat.land am bm)

@[expose] noncomputable def addM (ap am bp bm : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.xor am (Nat.land am (Nat.lor bp bm))) (Nat.xor bm (Nat.land bm (Nat.lor ap am))))
    (Nat.land ap bp)

@[expose] noncomputable def vadd (X Y : Nat) : Nat :=
  strictN (vP X) fun ap => strictN (vM X) fun am => strictN (vP Y) fun bp => strictN (vM Y) fun bm =>
    vmk (addP ap am bp bm) (addM ap am bp bm)

@[expose] noncomputable def vneg (Y : Nat) : Nat := vmk (vM Y) (vP Y)

@[expose] noncomputable def bit (x j : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight x j) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def mvL (L : List Nat) : Nat → Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat) (fun _ _ ap am => vmk ap am)
    (fun c _ ih xp xm ap am =>
      strictN (vP c) fun cp => strictN (vM c) fun cm =>
        nIf(Nat.beq (Nat.land xp (nat_lit 1)) (nat_lit 1),
          strictN (addP ap am cp cm) fun ap' => strictN (addM ap am cp cm) fun am' =>
            ih (Nat.shiftRight xp (nat_lit 1)) (Nat.shiftRight xm (nat_lit 1)) ap' am',
          nIf(Nat.beq (Nat.land xm (nat_lit 1)) (nat_lit 1),
            strictN (addP ap am cm cp) fun ap' => strictN (addM ap am cm cp) fun am' =>
              ih (Nat.shiftRight xp (nat_lit 1)) (Nat.shiftRight xm (nat_lit 1)) ap' am',
            ih (Nat.shiftRight xp (nat_lit 1)) (Nat.shiftRight xm (nat_lit 1)) ap am)))
    L

@[expose] noncomputable def mv (L : List Nat) (X : Nat) : Nat :=
  strictN (vP X) fun xp => strictN (vM X) fun xm => mvL L xp xm (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def key (K : Nat → Nat) (i : Nat) : Nat :=
  rget K (nat_lit 4) (nat_lit 15) (nat_lit 512) (mask (nat_lit 512)) i

@[expose] noncomputable def tab (T : Nat → Nat) (i : Nat) : Nat :=
  rget T (nat_lit 6) (nat_lit 63) (nat_lit 18) (mask (nat_lit 18)) i

@[expose] noncomputable def canon (X : Nat) : Bool :=
  strictB (vP X) fun p => strictB (vM X) fun m =>
    bAnd(Nat.beq (Nat.land p m) (nat_lit 0), bAnd(Nat.blt p (Nat.shiftLeft (nat_lit 1) (nat_lit 154)),
      Nat.blt m (Nat.shiftLeft (nat_lit 1) (nat_lit 154))))

@[expose] noncomputable def mvAt (K : Nat → Nat) (LA LB : List Nat) (A B : Nat → Nat) (n h : Nat) : Bool :=
  strictB (key K h) fun x => strictB (tab A h) fun a => strictB (tab B h) fun b =>
    bAnd(canon x, bAnd(Nat.blt a n, bAnd(Nat.blt b n,
      bAnd(Nat.beq (key K a) (mv LA x), Nat.beq (key K b) (mv LB x)))))

@[expose] noncomputable def mvRange (K : Nat → Nat) (LA LB : List Nat) (A B : Nat → Nat) (n lo cnt : Nat) : Bool :=
  allBlk lo (mvAt K LA LB A B n) cnt

@[expose] noncomputable def ordImg (a s : Nat) : Nat :=
  nIf(Nat.beq a s, Nat.succ s, nIf(Nat.blt a s, s, nat_lit 0))

@[expose] noncomputable def ordStep (A B : Nat → Nat) (h s : Nat) : Nat :=
  nIf(Nat.blt h s, strictN (ordImg (tab A h) s) fun s1 =>
    nIf(Nat.beq s1 (nat_lit 0), nat_lit 0, ordImg (tab B h) s1), nat_lit 0)

@[expose] noncomputable def ordRun (A B : Nat → Nat) (lo cnt s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ s => s)
    (fun _ ih h s => strictN (ordStep A B h s) fun s' => ih (Nat.succ h) s') cnt lo s

@[expose] noncomputable def sortAt (K SO SOI : Nat → Nat) (n i : Nat) : Bool :=
  strictB (tab SO i) fun x => bAnd(Nat.blt x n, bAnd(Nat.beq (tab SOI x) i,
    bIf(Nat.blt (Nat.succ i) n, Nat.blt (key K x) (key K (tab SO (Nat.succ i))), true)))

@[expose] noncomputable def sortRange (K SO SOI : Nat → Nat) (n lo cnt : Nat) : Bool :=
  allBlk lo (sortAt K SO SOI n) cnt

@[expose] noncomputable def trit (c : Nat) : Nat := Nat.mod (Nat.sub c (nat_lit 48)) (nat_lit 3)

@[expose] noncomputable def digitsK (cs : List Char) (R : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun _ p m => Nat.beq (vmk p m) R)
    (fun ch _ ih j p m => strictB (trit (Char.toNat ch)) fun t =>
      bIf(Nat.blt j (nat_lit 154),
        bIf(Nat.beq t (nat_lit 1), strictB (Nat.lor p (Nat.shiftLeft (nat_lit 1) j)) fun p' =>
            ih (Nat.succ j) p' m,
          bIf(Nat.beq t (nat_lit 2), strictB (Nat.lor m (Nat.shiftLeft (nat_lit 1) j)) fun m' =>
              ih (Nat.succ j) p m',
            ih (Nat.succ j) p m)),
        ih (Nat.succ j) p m))
    cs (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def wsK (c : Nat) : Bool :=
  bIf(Nat.beq c (nat_lit 32), true, bIf(Nat.beq c (nat_lit 9), true, bIf(Nat.beq c (nat_lit 10), true,
    bIf(Nat.beq c (nat_lit 13), true, bIf(Nat.beq c (nat_lit 11), true, Nat.beq c (nat_lit 12))))))

@[expose] noncomputable def entK (c : Nat) : Nat :=
  nIf(Nat.blt c (nat_lit 48), nat_lit 0, nIf(Nat.blt c (nat_lit 58), Nat.sub c (nat_lit 48), nat_lit 0))

@[expose] noncomputable def colEnt (C : Nat → Nat) (k e : Nat) : Bool :=
  strictB (Nat.div k (nat_lit 154)) fun i => strictB (Nat.mod k (nat_lit 154)) fun j =>
    strictB (C j) fun X => strictB (Nat.mod e (nat_lit 3)) fun t =>
      bAnd(Bool.rec (motive := fun _ => Bool) (Bool.not (Nat.beq t (nat_lit 1)))
          (Nat.beq t (nat_lit 1)) (bit (vP X) i),
        Bool.rec (motive := fun _ => Bool) (Bool.not (Nat.beq t (nat_lit 2)))
          (Nat.beq t (nat_lit 2)) (bit (vM X) i))

@[expose] noncomputable def colsBody (C : Nat → Nat) (cs : List Char) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool)
    (fun k => Nat.ble (nat_lit 23716) k)
    (fun ch _ ih k => strictB (Char.toNat ch) fun c =>
      bIf(wsK c, ih k,
        bIf(Nat.blt k (nat_lit 23716), bAnd(colEnt C k (entK c), ih (Nat.succ k)), ih (Nat.succ k))))
    cs

@[expose] noncomputable def colsHead (C : Nat → Nat) (cs : List Char) : Bool :=
  List.rec (motive := fun _ => Bool) (Nat.ble (nat_lit 23716) (nat_lit 0))
    (fun ch rest ih => bIf(Nat.beq (Char.toNat ch) (nat_lit 10), colsBody C rest (nat_lit 0), ih)) cs

@[expose] noncomputable def colsK (C : Nat → Nat) (cs : List Char) : Bool :=
  bAnd(allN (nat_lit 154) fun j => canon (C j), colsHead C cs)

@[expose] noncomputable def trace (TT UU : Nat → Nat → Nat) (W L x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ v => v)
    (fun _ ih k v => strictN (fld(W, Nat.mul (nat_lit 4) k, nat_lit 15)) fun c =>
      strictN (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0), TT (Nat.shiftRight c (nat_lit 1)) v,
        UU (Nat.shiftRight c (nat_lit 1)) v)) fun v' => ih (Nat.succ k) v') L (nat_lit 0) x

@[expose] noncomputable def trAt (TT UU : Nat → Nat → Nat) (WC WL : Nat → Nat) (n nT j₀ x : Nat) :
    Bool :=
  bAnd(allBlk (nat_lit 0) (fun h => strictB (TT h x) fun y => bAnd(Nat.blt y n,
      bAnd(Nat.blt (UU h x) n, Nat.beq (UU h y) x))) nT,
    allBlk j₀ (fun j => Nat.beq (TT j x) (trace TT UU (WC j) (WL j) x)) (Nat.sub nT j₀))

@[expose] noncomputable def trRange (TT UU : Nat → Nat → Nat) (WC WL : Nat → Nat) (n nT j₀ lo cnt : Nat) :
    Bool :=
  allBlk lo (trAt TT UU WC WL n nT j₀) cnt

end CFSG.KS.ON

end
