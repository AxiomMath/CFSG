module

public import Certificates.Data.Kernel.SporSch.PairJ3Cnt
public import Certificates.Data.Kernel.SporSch.PairCl

public section

namespace CFSG.KS.HS2272

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch

@[expose] noncomputable def wv (L : Nat → Nat → Nat) (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x) (fun k _ ih x => L k (ih x)) w x

@[expose] noncomputable def ivL (k : Nat) : Nat :=
  nIf(Nat.beq (Nat.mod k (nat_lit 2)) (nat_lit 0), Nat.succ k, Nat.pred k)

@[expose] noncomputable def wvI (L : Nat → Nat → Nat) (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun k _ ih x => strictN (L (ivL k) x) ih) w x

@[expose] noncomputable def cjv (L : Nat → Nat → Nat) (w : List Nat) (f : Nat → Nat) (x : Nat) :
    Nat :=
  wv L w (f (wvI L w x))

@[expose] noncomputable def eqBlk (lo len : Nat) (f g : Nat → Nat) : Bool :=
  allBlk lo (fun x => Nat.beq (f x) (g x)) len

@[expose] noncomputable def neL (bs : List Nat) (f g : Nat → Nat) : Bool :=
  bIf(eqOnL bs f g, false, true)

@[expose] noncomputable def cntFix (n : Nat) (f : Nat → Nat) : Nat :=
  foldN n (fun x s => nIf(Nat.beq (f x) x, Nat.succ s, s)) (nat_lit 0)

@[expose] noncomputable def cfL (n : Nat) (L : Nat → Nat → Nat) (f : Nat → Nat)
    (ws : List (List Nat)) (k : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih k => strictB (keyL n (cjv L w f) [nat_lit 1, nat_lit 2, nat_lit 3]) (fun k' =>
      bAnd(Nat.beq (cjv L w f (nat_lit 0)) (nat_lit 0), bAnd(Nat.blt k k', ih k')))) ws k

@[expose] noncomputable def fixG (L : Nat → Nat → Nat) (ws : List (List Nat)) (bs : List Nat) :
    Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => bAnd(eqOnL bs (wv L w) (fun x => x), ih)) ws

@[expose] noncomputable def hasBit (m p : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight m p) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def orbL (n : Nat) (L : Nat → Nat → Nat) (gs : List (List Nat))
    (es : List (Nat × Nat × Nat)) (m : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih m => bAnd(hasBit m e.2.1, bAnd(bIf(hasBit m e.1, false, true),
      bAnd(Nat.blt e.1 n, bAnd(Nat.beq (wv L (gs.getD e.2.2 []) e.2.1) e.1,
        ih (Nat.lor m (Nat.shiftLeft (nat_lit 1) e.1))))))) es m

@[expose] noncomputable def evenOrd (bs : List Nat) (f : Nat → Nat) (m : Nat) : Bool :=
  bAnd(Nat.beq (Nat.mod m (nat_lit 2)) (nat_lit 0), bAnd(Nat.blt (nat_lit 0) m,
    bAnd(eqOnL bs (powF f m) (fun x => x),
      neL bs (powF f (Nat.div m (nat_lit 2))) (fun x => x))))

@[expose] noncomputable def conjProd (L : Nat → Nat → Nat) (x y : List Nat) (p : Nat) : Nat :=
  wv L x (wv L y (wv L x (wvI L y p)))

@[expose] noncomputable def ord6L (bs : List Nat) (f : Nat → Nat) : Bool :=
  bAnd(eqOnL bs (powF f (nat_lit 6)) (fun x => x), bAnd(neL bs (powF f (nat_lit 3)) (fun x => x),
    neL bs (powF f (nat_lit 2)) (fun x => x)))

@[expose] noncomputable def chainL (n : Nat) (L : Nat → Nat → Nat)
    (levs : List (Nat × List (List Nat) × List (Nat × Nat × Nat))) (prev : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun v _ ih prev => bAnd(fixG L v.2.1 prev, bAnd(Nat.blt v.1 n,
      bAnd(orbL n L v.2.1 v.2.2 (Nat.shiftLeft (nat_lit 1) v.1), ih (v.1 :: prev))))) levs prev

@[expose] noncomputable def witL (bs : List Nat) (L : Nat → Nat → Nat) (y : List Nat)
    (hm : List Nat × Nat) : Bool :=
  evenOrd bs (conjProd L y hm.1) hm.2

@[expose] noncomputable def oddE (bs : List Nat) (L : Nat → Nat → Nat)
    (e : Nat × List (List Nat) × List (List Nat × Nat)) : Bool :=
  bIf(Nat.beq e.2.1.length (nat_lit 1),
    bAnd(ordPL bs (wv L (e.2.1.getD 0 [])) e.1, witL bs L (e.2.1.getD 0 []) (e.2.2.getD 0 ([], 0))),
    bAnd(Nat.beq e.2.1.length (nat_lit 2), bAnd(Nat.beq e.1 (nat_lit 3),
      bAnd(ordPL bs (wv L (e.2.1.getD 0 [])) (nat_lit 3),
      bAnd(ordPL bs (wv L (e.2.1.getD 1 [])) (nat_lit 3),
      bAnd(eqOnL bs (wv L (e.2.1.getD 0 [] ++ e.2.1.getD 1 []))
        (wv L (e.2.1.getD 1 [] ++ e.2.1.getD 0 [])),
      bAnd(neL bs (wv L (e.2.1.getD 1 [])) (wv L (e.2.1.getD 0 [])),
      bAnd(neL bs (wv L (e.2.1.getD 1 [])) (wv L (e.2.1.getD 0 [] ++ e.2.1.getD 0 [])),
      bAnd(witL bs L (e.2.1.getD 0 []) (e.2.2.getD 0 ([], 0)),
      bAnd(witL bs L (e.2.1.getD 1 []) (e.2.2.getD 1 ([], 0)),
      bAnd(witL bs L (e.2.1.getD 0 [] ++ e.2.1.getD 1 []) (e.2.2.getD 2 ([], 0)),
        witL bs L (e.2.1.getD 0 [] ++ e.2.1.getD 1 [] ++ e.2.1.getD 1 [])
          (e.2.2.getD 3 ([], 0)))))))))))))

@[expose] noncomputable def oddL (bs : List Nat) (L : Nat → Nat → Nat)
    (ods : List (Nat × List (List Nat) × List (List Nat × Nat))) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih => bAnd(oddE bs L e, ih)) ods

@[expose] noncomputable def sortK (N : Nat) (K S SI : Nat → Nat) : Bool :=
  bAnd(allN N (fun i => bAnd(Nat.blt (SI i) N, bAnd(Nat.blt (S i) N, Nat.beq (S (SI i)) i))),
    allN (Nat.sub N (nat_lit 1)) (fun j => Nat.blt (K (S j)) (K (S (Nat.succ j)))))

end CFSG.KS.HS2272

end
