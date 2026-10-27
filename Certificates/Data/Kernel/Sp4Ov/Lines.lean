module

public import Certificates.Data.Kernel.Sp4Ov.Kit

public section

namespace CFSG.KD.Sp4Ov

open CFSG.KC.Loop

abbrev SpecR := Nat × Nat × Nat × Nat × Nat

@[expose] noncomputable def allMems (tr : List Nat) (f : Nat → Bool) : Bool :=
  bAnd(f oneP, List.rec (motive := fun _ => Bool) true
    (fun e _ ih => bAnd(f fld(e, nat_lit 0, nat_lit 65535), ih)) tr)

@[expose] noncomputable def anyMems (tr : List Nat) (f : Nat → Bool) : Bool :=
  bIf(f oneP, true, List.rec (motive := fun _ => Bool) false
    (fun e _ ih => bIf(f fld(e, nat_lit 0, nat_lit 65535), true, ih)) tr)

@[expose] noncomputable def foldMems (tr : List Nat) (f : Nat → Nat → Nat) (acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun e _ ih acc => strictN (f fld(e, nat_lit 0, nat_lit 65535) acc) ih) tr (f oneP acc)

@[expose] noncomputable def sizeK (s : NodeR) : Nat :=
  foldMems s.tree (fun _ acc => Nat.add acc (nat_lit 1)) (nat_lit 0)

@[expose] noncomputable def onL (l z : Nat) : Bool :=
  bIf(Nat.beq z fld(l, nat_lit 0, nat_lit 15), true,
    bIf(Nat.beq z fld(l, nat_lit 4, nat_lit 15), true, Nat.beq z fld(l, nat_lit 8, nat_lit 15)))

@[expose] noncomputable def stabK (x l : Nat) : Bool :=
  bAnd(onL l (mv x fld(l, nat_lit 0, nat_lit 15)), bAnd(onL l (mv x fld(l, nat_lit 4, nat_lit 15)),
    onL l (mv x fld(l, nat_lit 8, nat_lit 15))))

@[expose] noncomputable def fixK (x l : Nat) : Bool :=
  bAnd(Nat.beq (mv x fld(l, nat_lit 0, nat_lit 15)) fld(l, nat_lit 0, nat_lit 15),
    bAnd(Nat.beq (mv x fld(l, nat_lit 4, nat_lit 15)) fld(l, nat_lit 4, nat_lit 15),
      Nat.beq (mv x fld(l, nat_lit 8, nat_lit 15)) fld(l, nat_lit 8, nat_lit 15)))

@[expose] noncomputable def ord3K (x : Nat) : Bool :=
  bIf(Nat.beq x oneP, false, Nat.beq (mulP x (mulP x x)) oneP)

@[expose] noncomputable def invlK (x : Nat) : Bool :=
  bIf(Nat.beq x oneP, false, Nat.beq (mulP x x) oneP)

@[expose] noncomputable def commK (x y : Nat) : Bool := Nat.beq (mulP x y) (mulP y x)

@[expose] noncomputable def cntStep (l x acc : Nat) : Nat :=
  Nat.lor (Nat.add (Nat.add acc (nat_lit 4294967296))
      (nIf(stabK x l, Nat.add (nat_lit 1) (nIf(fixK x l, nat_lit 65536, nat_lit 0)), nat_lit 0)))
    (nIf(bAnd(stabK x l, bIf(fixK x l, false, true)),
      Nat.lor (nIf(ord3K x, nat_lit 281474976710656, nat_lit 0))
        (nIf(invlK x, nat_lit 562949953421312, nat_lit 0)), nat_lit 0))

@[expose] noncomputable def cntK (s : NodeR) (l : Nat) : Nat := foldMems s.tree (cntStep l) (nat_lit 0)

@[expose] noncomputable def feasK (c : Nat) : Bool :=
  bAnd(Nat.beq (Nat.mod fld(c, nat_lit 0, nat_lit 65535) (Nat.gcd fld(c, nat_lit 32, nat_lit 65535)
      (nat_lit 16))) (nat_lit 0),
    bAnd(Nat.beq fld(c, nat_lit 48, nat_lit 1) (nat_lit 1),
      bAnd(Nat.blt fld(c, nat_lit 0, nat_lit 65535) fld(c, nat_lit 32, nat_lit 65535),
        Nat.beq fld(c, nat_lit 49, nat_lit 1) (nat_lit 1))))

@[expose] noncomputable def fixList (s : NodeR) (l : Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat)
    (Bool.rec (motive := fun _ => List Nat) [] [oneP] (fixK oneP l))
    (fun e _ ih => Bool.rec (motive := fun _ => List Nat) ih (fld(e, nat_lit 0, nat_lit 65535) :: ih)
      (fixK fld(e, nat_lit 0, nat_lit 65535) l)) s.tree

@[expose] noncomputable def centCnt (F : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun f _ ih => Nat.add (nIf(commK f x, nat_lit 1, nat_lit 0)) ih) F

@[expose] noncomputable def ncAny (F : List Nat) (y : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun f _ ih => bIf(commK f y, ih, true)) F

@[expose] noncomputable def factK (s : NodeR) (l X : Nat) : Bool :=
  allMems s.tree fun x => bAnd(bIf(fixK x l, memP X x, true),
    bIf(bAnd(stabK x l, bIf(fixK x l, false, true)), bIf(bAnd(memP X x, ord3K x), false, true),
      true))

@[expose] noncomputable def s120K (s : NodeR) (l m60 : Nat) : Bool :=
  (fun F => allMems s.tree fun x => bAnd(bIf(fixK x l, memP m60 x, true),
    bIf(bAnd(stabK x l, bAnd(bIf(fixK x l, false, true), invlK x)),
      Nat.beq (centCnt F x) (nat_lit 2), true))) (fixList s l)

@[expose] noncomputable def s720K (s : NodeR) (l : Nat) : Bool :=
  (fun F => allMems s.tree fun y => bIf(fixK y l, true, ncAny F y)) (fixList s l)

@[expose] noncomputable def conclK (sp : SpecR) (s : NodeR) (l c : Nat) : Bool :=
  (fun n nF => bIf(Nat.beq n (nat_lit 18), true,
    bIf(bAnd(Nat.beq n (nat_lit 36), bAnd(Nat.beq s.mask sp.1, bAnd(Nat.beq nF (nat_lit 2),
        bIf(factK s l sp.2.1, true, factK s l sp.2.2.1)))), true,
    bIf(bAnd(Nat.beq n (nat_lit 120), bAnd(Nat.beq s.mask sp.2.2.2.1, s120K s l sp.2.2.2.2)), true,
    bIf(bAnd(Nat.beq n (nat_lit 360), Nat.beq nF (nat_lit 4)), true,
      bAnd(Nat.beq n (nat_lit 720), bAnd(Nat.beq nF (nat_lit 8), s720K s l)))))))
  fld(c, nat_lit 32, nat_lit 65535) fld(c, nat_lit 16, nat_lit 65535)

@[expose] noncomputable def lineOneK (sp : SpecR) (s : NodeR) (l : Nat) : Bool :=
  (fun c => bIf(feasK c, conclK sp s l c, true)) (cntK s l)

@[expose] noncomputable def lineK (sp : SpecR) (L : List NodeR) (lines : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun s _ ih => bAnd(
    List.rec (motive := fun _ => Bool) true (fun l _ ih2 => bAnd(lineOneK sp s l, ih2)) lines, ih)) L

@[expose] noncomputable def qK (a x : Nat) : Nat :=
  (fun t => Nat.land (Nat.xor (Nat.xor (Nat.xor t (Nat.shiftRight t (nat_lit 1)))
      (Nat.xor (Nat.shiftRight t (nat_lit 2)) (Nat.shiftRight t (nat_lit 3))))
    (Nat.xor (Nat.land x (Nat.shiftRight x (nat_lit 3)))
      (Nat.land (Nat.shiftRight x (nat_lit 1)) (Nat.shiftRight x (nat_lit 2))))) (nat_lit 1))
  (Nat.land a x)

@[expose] noncomputable def qZero (a l : Nat) : Bool :=
  bAnd(Nat.beq (qK a fld(l, nat_lit 0, nat_lit 15)) (nat_lit 0),
    bAnd(Nat.beq (qK a fld(l, nat_lit 4, nat_lit 15)) (nat_lit 0),
      Nat.beq (qK a fld(l, nat_lit 8, nat_lit 15)) (nat_lit 0)))

@[expose] noncomputable def any16 (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun v ih => bIf(f v, true, ih)) (nat_lit 16)

@[expose] noncomputable def all16 (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun a ih => bAnd(f a, ih)) (nat_lit 16)

@[expose] noncomputable def movesQ (s : NodeR) (a : Nat) : Bool :=
  anyMems s.tree fun d => any16 fun v => bIf(Nat.beq (qK a (mv d v)) (qK a v), false, true)

@[expose] noncomputable def quadK (sp : SpecR) (L : List NodeR) (lines : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun s _ ih => bAnd(
    bIf(bIf(Nat.beq s.mask sp.2.2.2.1, true, Nat.ble (nat_lit 360) (sizeK s)),
      all16 fun a => bIf(List.rec (motive := fun _ => Bool) false
        (fun l _ ih2 => bIf(qZero a l, true, ih2)) lines, movesQ s a, true), true), ih)) L

@[expose] noncomputable def isLine (u v l : Nat) : Bool :=
  bAnd(onL l u, bAnd(onL l v, onL l (Nat.xor u v)))

@[expose] noncomputable def linesOK (lines : List Nat) : Bool :=
  all16 fun u => all16 fun v =>
    bIf(bAnd(Nat.blt (nat_lit 0) u, bAnd(Nat.blt (nat_lit 0) v, bAnd(bIf(Nat.beq u v, false, true),
        Nat.beq (bJK u v) (nat_lit 0)))),
      List.rec (motive := fun _ => Bool) false (fun l _ ih => bIf(isLine u v l, true, ih)) lines,
      true)

end CFSG.KD.Sp4Ov

end
