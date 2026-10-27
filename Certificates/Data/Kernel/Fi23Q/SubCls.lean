module

public import Certificates.Data.Kernel.Pc3.Coll

public section

namespace CFSG.KC.Fi23Q

open CFSG.KC.Enum CFSG.KC.Pc3

@[expose] noncomputable def add3B (al ah bl bh : Nat) : Nat :=
  (fun az bz => Nat.lor
      (Nat.lor (Nat.land az bl) (Nat.lor (Nat.land al bz) (Nat.land ah bh)))
      (Nat.shiftLeft (Nat.lor (Nat.land az bh) (Nat.lor (Nat.land ah bz) (Nat.land al bl)))
        (nat_lit 1)))
    (Nat.xor (nat_lit 341) (Nat.lor al ah)) (Nat.xor (nat_lit 341) (Nat.lor bl bh))

@[expose] noncomputable def add3 (u v : Nat) : Nat :=
  add3B (Nat.land u (nat_lit 341)) (Nat.land (Nat.shiftRight u (nat_lit 1)) (nat_lit 341))
    (Nat.land v (nat_lit 341)) (Nat.land (Nat.shiftRight v (nat_lit 1)) (nat_lit 341))

@[expose] noncomputable def neg3 (u : Nat) : Nat :=
  Nat.lor (Nat.shiftLeft (Nat.land u (nat_lit 341)) (nat_lit 1))
    (Nat.land (Nat.shiftRight u (nat_lit 1)) (nat_lit 341))

@[expose] noncomputable def smul3 (e u : Nat) : Nat :=
  nIf(Nat.beq e (nat_lit 0), nat_lit 0, nIf(Nat.beq e (nat_lit 1), u, neg3 u))

@[expose] noncomputable def sub3 (u v : Nat) : Nat := add3 u (neg3 v)

@[expose] noncomputable def dot3 (u v : Nat) : Nat :=
  Nat.mod (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.add acc (Nat.mul (dg u k) (dg v k))) (nat_lit 5)) (nat_lit 3)

@[expose] noncomputable def colE (CJ k c : Nat) : Nat :=
  Nat.shiftRight (f32 CJ (Nat.add (Nat.shiftLeft k (nat_lit 4)) (Nat.add (nat_lit 4) c)))
    (nat_lit 8)

@[expose] noncomputable def mE (CJ k w : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c acc => add3 acc (smul3 (dg w c) (colE CJ k c))) (nat_lit 5)

@[expose] noncomputable def mT (CJ a w : Nat) : Nat :=
  rep (dg a (nat_lit 3)) (mE CJ (nat_lit 3)) (rep (dg a (nat_lit 2)) (mE CJ (nat_lit 2))
    (rep (dg a (nat_lit 1)) (mE CJ (nat_lit 1)) (rep (dg a (nat_lit 0)) (mE CJ (nat_lit 0)) w)))

@[expose] noncomputable def colM (Mt a c : Nat) : Nat :=
  fld(Mt, Nat.mul (nat_lit 10) (Nat.add (Nat.mul (nat_lit 5) a) c), nat_lit 1023)

@[expose] noncomputable def mC (Mt a w : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c acc => add3 acc (smul3 (dg w c) (colM Mt a c))) (nat_lit 5)

@[expose] noncomputable def rT (R a k : Nat) : Nat :=
  fld(R, Nat.shiftLeft (Nat.add (Nat.shiftLeft a (nat_lit 2)) k) (nat_lit 3), nat_lit 255)

@[expose] noncomputable def muT (R a b : Nat) : Nat :=
  rep (dg b (nat_lit 3)) (fun x => rT R x (nat_lit 3)) (rep (dg b (nat_lit 2)) (fun x => rT R x (nat_lit 2))
    (rep (dg b (nat_lit 1)) (fun x => rT R x (nat_lit 1)) (rep (dg b (nat_lit 0)) (fun x => rT R x (nat_lit 0)) a)))

@[expose] noncomputable def bitM (m a : Nat) : Bool := Nat.beq (fld(m, a, nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def anyN (n : Nat) (f : Nat → Bool) : Bool := !(allN n fun i => !(f i))

@[expose] noncomputable def vec3 (d i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.add acc (Nat.shiftLeft (Nat.mod (Nat.div i (Nat.pow (nat_lit 3) k)) (nat_lit 3))
      (Nat.shiftLeft k (nat_lit 1)))) d

@[expose] noncomputable def allT (f : Nat → Bool) : Bool :=
  allN (nat_lit 81) fun i => strictB (vec3 (nat_lit 4) i) f

@[expose] noncomputable def allE (f : Nat → Bool) : Bool :=
  allN (nat_lit 243) fun i => strictB (vec3 (nat_lit 5) i) f

@[expose] noncomputable def foldT (f : Nat → Nat → Nat) (s : Nat) : Nat :=
  foldN (nat_lit 81) (fun i acc => strictN (vec3 (nat_lit 4) i) fun a => f a acc) s

@[expose] noncomputable def clsEK (CJ : Nat) : Bool :=
  allN (nat_lit 9) fun i => allN (nat_lit 9) fun j => bIf(Nat.blt i j,
    bIf(Nat.blt i (nat_lit 4),
      bIf(Nat.ble (nat_lit 4) j, Nat.beq (lowV (f32 CJ (Nat.add (Nat.shiftLeft i (nat_lit 4)) j))
        (nat_lit 4)) (nat_lit 0), true),
      Nat.beq (f32 CJ (Nat.add (Nat.shiftLeft i (nat_lit 4)) j))
        (Nat.shiftLeft (nat_lit 1) (Nat.shiftLeft j (nat_lit 1)))), true)

@[expose] noncomputable def clsRK (PW CJ R : Nat) : Bool :=
  allT fun a => allN (nat_lit 4) fun k =>
    Nat.beq (rT R a k) (lowV (mulV PW CJ (nat_lit 9) a
      (Nat.shiftLeft (nat_lit 1) (Nat.shiftLeft k (nat_lit 1)))) (nat_lit 4))

@[expose] noncomputable def clsMK (CJ Mt : Nat) : Bool :=
  allT fun a => allN (nat_lit 5) fun c =>
    Nat.beq (colM Mt a c) (mT CJ a (Nat.shiftLeft (nat_lit 1) (Nat.shiftLeft c (nat_lit 1))))

@[expose] noncomputable def commH (R m a : Nat) : Bool :=
  allT fun h => bIf(bitM m h, Nat.beq (muT R a h) (muT R h a), true)

@[expose] noncomputable def closM (R m a a2 : Nat) : Nat :=
  foldT (fun h acc => nIf(bitM m h,
    Nat.lor acc (Nat.lor (Nat.shiftLeft (nat_lit 1) h) (Nat.lor (Nat.shiftLeft (nat_lit 1) (muT R a h))
      (Nat.shiftLeft (nat_lit 1) (muT R a2 h)))), acc)) (nat_lit 0)

@[expose] noncomputable def clsLK (R : Nat) (L : List Nat) : Bool :=
  bAnd(Nat.beq (L.getD (nat_lit 0) (nat_lit 0)) (nat_lit 1),
    allN L.length fun i => strictB (L.getD i (nat_lit 0)) fun m => bAnd(bitM m (nat_lit 0), allT fun a =>
      bIf(bitM m a, true, strictB (muT R a a) fun a2 => bIf(Nat.beq (muT R a2 a) (nat_lit 0),
        bIf(commH R m a,
          strictB (closM R m a a2) fun X => anyN L.length fun j => Nat.beq (L.getD j (nat_lit 0)) X,
        true), true))))

@[expose] noncomputable def f8 (b j : Nat) : Nat :=
  fld(b, Nat.shiftLeft j (nat_lit 3), nat_lit 255)

@[expose] noncomputable def fixB (Mt bd w : Nat) : Bool :=
  allN (f8 bd (nat_lit 0)) fun j => Nat.beq (mC Mt (f8 bd (Nat.succ j)) w) w

@[expose] noncomputable def cntC (Mt bd : Nat) : Nat :=
  foldN (nat_lit 243) (fun i acc => strictN (vec3 (nat_lit 5) i) fun w =>
    nIf(fixB Mt bd w, Nat.succ acc, acc)) (nat_lit 0)

@[expose] noncomputable def popc (m : Nat) : Nat :=
  foldT (fun h acc => nIf(bitM m h, Nat.succ acc, acc)) (nat_lit 0)

@[expose] noncomputable def clsCK (Mt : Nat) (L B : List Nat) : Bool :=
  allN (Nat.sub L.length (nat_lit 1)) fun i => (fun m bd =>
    bAnd(allN (f8 bd (nat_lit 0)) fun j => bitM m (f8 bd (Nat.succ j)),
      Nat.ble (Nat.mul (popc m) (cntC Mt bd)) (nat_lit 81)))
    (L.getD (Nat.succ i) (nat_lit 0)) (B.getD (Nat.succ i) (nat_lit 0))

@[expose] noncomputable def clsGK (Mt : Nat) (NPV B K X : List Nat) : Bool :=
  allN K.length fun i => bIf(Nat.beq (K.getD i (nat_lit 0)) (nat_lit 1),
    (fun g => bAnd(Nat.blt g NPV.length, (fun u => bAnd(Nat.beq (lowV u (nat_lit 4)) (nat_lit 0),
      fixB Mt (B.getD i (nat_lit 0)) (Nat.shiftRight u (nat_lit 8)))) (NPV.getD g (nat_lit 0))))
      (X.getD i (nat_lit 0)), true)

@[expose] noncomputable def clsHK (NPV : List Nat) : Bool :=
  allE fun f => bIf(Nat.beq f (nat_lit 0), true,
    anyN NPV.length fun k => (fun u => bAnd(Nat.beq (lowV u (nat_lit 4)) (nat_lit 0),
      Nat.beq (dot3 f (Nat.shiftRight u (nat_lit 8))) (nat_lit 0))) (NPV.getD k (nat_lit 0)))

@[expose] noncomputable def cubeE (Mt b t w : Nat) : Bool :=
  Nat.beq (add3 t (add3 w (add3 (mC Mt b w) (mC Mt b (mC Mt b w))))) (nat_lit 0)

@[expose] noncomputable def covE (NPV : List Nat) (fin : Nat → Bool) (b w : Nat) : Bool :=
  anyN NPV.length fun k => (fun u => bAnd(Nat.beq (lowV u (nat_lit 4)) b,
    fin (sub3 (Nat.shiftRight u (nat_lit 8)) w))) (NPV.getD k (nat_lit 0))

@[expose] noncomputable def cubeV (PW CJ x : Nat) : Nat :=
  mulV PW CJ (nat_lit 9) (mulV PW CJ (nat_lit 9) x x) x

@[expose] noncomputable def bad2 (PW CJ Mt : Nat) (NPV : List Nat) (m bd b : Nat) : Bool :=
  bAnd(bitM m b, strictB (cubeV PW CJ b) fun y => bAnd(Nat.beq (lowV y (nat_lit 4)) (nat_lit 0),
    strictB (Nat.shiftRight y (nat_lit 8)) fun t =>
    allE fun w => bIf(cubeE Mt b t w, covE NPV (fixB Mt bd) b w, true)))

@[expose] noncomputable def clsAK (PW CJ Mt : Nat) (NPV L B K X : List Nat) : Bool :=
  allN K.length fun i => bIf(Nat.beq (K.getD i (nat_lit 0)) (nat_lit 2),
    bad2 PW CJ Mt NPV (L.getD i (nat_lit 0)) (B.getD i (nat_lit 0)) (X.getD i (nat_lit 0)), true)

@[expose] noncomputable def commE (Mt ai aj g wi wj : Nat) : Bool :=
  Nat.beq (add3 g (add3 (mC Mt aj wi) wj)) (add3 (mC Mt ai wj) wi)

@[expose] noncomputable def inC1 (c d : Nat) : Bool :=
  bIf(Nat.beq d (nat_lit 0), true, bIf(Nat.beq d c, true, Nat.beq d (add3 c c)))

@[expose] noncomputable def bad3L (Mt : Nat) (NPV : List Nat) (a1 a2 a3 c p t1 t2 t3 g12 g13 g23 : Nat) :
    Bool :=
  allE fun w1 => bIf(bAnd(Nat.beq (dg w1 p) (nat_lit 0),
      bAnd(cubeE Mt a1 t1 w1, !(covE NPV (inC1 c) a1 w1))),
    allE fun w2 => bIf(bAnd(Nat.beq (dg w2 p) (nat_lit 0),
        bAnd(cubeE Mt a2 t2 w2, bAnd(commE Mt a1 a2 g12 w1 w2, !(covE NPV (inC1 c) a2 w2)))),
      allE fun w3 => bIf(bAnd(Nat.beq (dg w3 p) (nat_lit 0),
          bAnd(cubeE Mt a3 t3 w3, bAnd(commE Mt a1 a3 g13 w1 w3, commE Mt a2 a3 g23 w2 w3))),
        covE NPV (inC1 c) a3 w3, true), true), true)

@[expose] noncomputable def cubeK (PW CJ a : Nat) (k : Nat → Bool) : Bool :=
  strictB (cubeV PW CJ a) fun y =>
    bAnd(Nat.beq (lowV y (nat_lit 4)) (nat_lit 0), k (Nat.shiftRight y (nat_lit 8)))

@[expose] noncomputable def commK (PW CJ a b : Nat) (k : Nat → Bool) : Bool :=
  strictB (mulV PW CJ (nat_lit 9) a b) fun u => strictB (mulV PW CJ (nat_lit 9) b a) fun v =>
    bAnd(Nat.beq (lowV u (nat_lit 4)) (lowV v (nat_lit 4)),
      k (sub3 (Nat.shiftRight u (nat_lit 8)) (Nat.shiftRight v (nat_lit 8))))

@[expose] noncomputable def bad3 (PW CJ Mt : Nat) (NPV : List Nat) (m bd a1 a2 a3 c p : Nat) : Bool :=
  bAnd(bitM m a1, bAnd(bitM m a2, bAnd(bitM m a3, bAnd(!(Nat.beq c (nat_lit 0)),
    bAnd(Nat.beq (dg c p) (nat_lit 1), bAnd(Nat.blt p (nat_lit 5), bAnd(fixB Mt bd c,
    cubeK PW CJ a1 fun t1 => cubeK PW CJ a2 fun t2 => cubeK PW CJ a3 fun t3 =>
    commK PW CJ a1 a2 fun g12 => commK PW CJ a1 a3 fun g13 => commK PW CJ a2 a3 fun g23 =>
    strictB t1 fun t1 => strictB t2 fun t2 => strictB t3 fun t3 =>
    strictB g12 fun g12 => strictB g13 fun g13 => strictB g23 fun g23 =>
    bad3L Mt NPV a1 a2 a3 c p t1 t2 t3 g12 g13 g23)))))))

@[expose] noncomputable def clsBK (PW CJ Mt : Nat) (NPV L B K D3 : List Nat) : Bool :=
  allN K.length fun i => bIf(Nat.beq (K.getD i (nat_lit 0)) (nat_lit 3),
    bad3 PW CJ Mt NPV (L.getD i (nat_lit 0)) (B.getD i (nat_lit 0)) (D3.getD (nat_lit 0) (nat_lit 0))
      (D3.getD (nat_lit 1) (nat_lit 0)) (D3.getD (nat_lit 2) (nat_lit 0)) (D3.getD (nat_lit 3) (nat_lit 0))
      (D3.getD (nat_lit 4) (nat_lit 0)), true)

@[expose] noncomputable def clsKK (L K : List Nat) : Bool :=
  bAnd(Nat.beq K.length L.length, bAnd(Nat.beq (K.getD (nat_lit 0) (nat_lit 0)) (nat_lit 0),
    allN (Nat.sub K.length (nat_lit 1)) fun i => bAnd(Nat.ble (nat_lit 1) (K.getD (Nat.succ i) (nat_lit 0)),
      Nat.ble (K.getD (Nat.succ i) (nat_lit 0)) (nat_lit 3))))

end CFSG.KC.Fi23Q

end
