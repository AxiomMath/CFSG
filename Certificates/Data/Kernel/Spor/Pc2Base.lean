module

public import Certificates.Data.Kernel.Spor.CommBase

public section

namespace CFSG.KC.Pc2Base

open CFSG.KC.Enum CFSG.KC.CommBase

@[expose] noncomputable def bit (e k : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight e k) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def p2 (k : Nat) : Nat := Nat.shiftLeft (nat_lit 1) k

@[expose] noncomputable def hiOnly (e k : Nat) : Bool :=
  Nat.beq (Nat.land e (Nat.sub (p2 k) (nat_lit 1))) (nat_lit 0)

@[expose] noncomputable def wW (e k m : Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih k => Bool.rec (motive := fun _ => List Nat) (ih (Nat.add k (nat_lit 1)))
      (k :: ih (Nat.add k (nat_lit 1))) (bit e k)) m k

@[expose] noncomputable def rel (R : List (List Nat)) (k j : Nat) : Nat := (R.getD k []).getD j 0

@[expose] noncomputable def mx (R : List (List Nat)) (n m k v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.xor acc (nIf(bit v i, Nat.shiftRight (rel R k (Nat.add m i)) m, nat_lit 0)))
    (Nat.sub n m)

@[expose] noncomputable def mw (R : List (List Nat)) (n m : Nat) (W : List Nat) (v : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) v (fun z _ ih => mx R n m z ih) W

@[expose] noncomputable def dt (K a b : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun i acc => Bool.rec (motive := fun _ => Bool) acc (notB acc) (bit (Nat.land a b) i)) K

@[expose] noncomputable def wEq (w mk : Nat) (L : Nat → Nat) (B U V : List Nat) : Bool :=
  allL (fun b => Nat.beq (wapp w mk L U b) (wapp w mk L V b)) B

@[expose] noncomputable def shapeOK (R : List (List Nat)) (n m : Nat) : Bool :=
  allN n (fun k => allN n (fun j => bIf(Nat.blt j k, true, strictB (rel R k j) (fun e =>
    bAnd(Nat.blt e (p2 n), bAnd(hiOnly e (Nat.add k (nat_lit 1)),
      bIf(Nat.blt k m, bIf(Nat.blt j m, true, hiOnly e m),
        bIf(Nat.beq j k, Nat.beq e (nat_lit 0), Nat.beq e (p2 j)))))))))

@[expose] noncomputable def relOK (w mk : Nat) (L : Nat → Nat) (B : List Nat) (R : List (List Nat))
    (n : Nat) : Bool :=
  allN n (fun k => allN n (fun j => bIf(Nat.blt j k, true,
    bIf(Nat.beq j k, wEq w mk L B [k, k] (wW (rel R k k) (nat_lit 0) n),
      wEq w mk L B [k, j] (List.append (wW (rel R k j) (nat_lit 0) n) [k])))))

@[expose] noncomputable def memL (O : List Nat) (y : Nat) : Bool := anyL (fun o => Nat.beq o y) O

@[expose] noncomputable def sepK (N w mk : Nat) (L : Nat → Nat) (n k v x : Nat) (O : List Nat) :
    Bool :=
  bAnd(Nat.beq (pg w mk (L k) x) v, bAnd(memL O v, bAnd(notB (memL O x), bAnd(Nat.blt x N,
    allL (fun y => bAnd(Nat.blt y N, allN n (fun j => bIf(Nat.blt k j, memL O (pg w mk (L j) y),
      true)))) O))))

@[expose] noncomputable def sepOK (N w mk : Nat) (L : Nat → Nat) (n : Nat)
    (SEP : List (Nat × Nat × List Nat)) : Bool :=
  allN n (fun k => sepK N w mk L n k (SEP.getD k (0, 0, [])).1 (SEP.getD k (0, 0, [])).2.1
    (SEP.getD k (0, 0, [])).2.2)

@[expose] noncomputable def coK (w mk : Nat) (L : Nat → Nat) (B : List Nat) (R : List (List Nat))
    (n m dI e f φ : Nat) : Bool :=
  bAnd(Nat.blt f (p2 n),
  bAnd(allL (fun b => Nat.beq (wapp w mk L (wW e (nat_lit 0) m) (wapp w mk L (wW e (nat_lit 0) m) b))
    (wapp w mk L (wW f (nat_lit 0) n) b)) B,
  bIf(hiOnly f m,
    bAnd(allN (Nat.sub n m) (fun j => notB (dt (Nat.sub n m) φ
      (Nat.xor (mw R n m (wW e (nat_lit 0) m) (p2 j)) (p2 j)))),
      dt (Nat.sub n m) φ (Nat.xor (p2 (Nat.sub dI m)) (Nat.shiftRight f m))),
    true)))

@[expose] noncomputable def coOK (w mk : Nat) (L : Nat → Nat) (B : List Nat) (R : List (List Nat))
    (n m dI : Nat) (CO : List (Nat × Nat)) : Bool :=
  allN (p2 m) (fun e => coK w mk L B R n m dI e (CO.getD e (0, 0)).1 (CO.getD e (0, 0)).2)

@[expose] noncomputable def inZ (m uI dI a : Nat) : Bool :=
  bIf(Nat.beq a (nat_lit 0), true, bIf(Nat.beq a (p2 (Nat.sub uI m)), true,
    bIf(Nat.beq a (p2 (Nat.sub dI m)), true,
      Nat.beq a (Nat.xor (p2 (Nat.sub uI m)) (p2 (Nat.sub dI m))))))

@[expose] noncomputable def cenOK (R : List (List Nat)) (n m uI dI : Nat) : Bool :=
  bAnd(allN (p2 m) (fun e => bIf(Nat.beq e (nat_lit 0), true,
    notB (allN (Nat.sub n m) (fun j => Nat.beq (mw R n m (wW e (nat_lit 0) m) (p2 j)) (p2 j))))),
  allN (p2 (Nat.sub n m)) (fun a => bIf(allN m (fun k => Nat.beq (mx R n m k a) a),
    inZ m uI dI a, notB (inZ m uI dI a))))

@[expose] noncomputable def witOK (w mk : Nat) (L : Nat → Nat) (B : List Nat) (n uI dI wit : Nat) :
    Bool :=
  allL (fun b => Nat.beq (wapp w mk L (wW wit (nat_lit 0) n) (wapp w mk L (wW wit (nat_lit 0) n) b))
    (pg w mk (L uI) (pg w mk (L dI) b))) B

@[expose] noncomputable def pc2OK (N w mk : Nat) (L : Nat → Nat) (B : List Nat) (n m uI dI : Nat)
    (R : List (List Nat)) (SEP : List (Nat × Nat × List Nat)) (CO : List (Nat × Nat)) (wit : Nat) :
    Bool :=
  bAnd(Nat.ble m dI, bAnd(Nat.blt dI n, bAnd(Nat.ble m uI, bAnd(Nat.blt uI n,
  bAnd(notB (Nat.beq uI dI),
  bAnd(shapeOK R n m, bAnd(relOK w mk L B R n, bAnd(sepOK N w mk L n SEP,
  bAnd(coOK w mk L B R n m dI CO, bAnd(cenOK R n m uI dI, witOK w mk L B n uI dI wit))))))))))

end CFSG.KC.Pc2Base

end
