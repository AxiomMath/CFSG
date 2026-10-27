module

public import Certificates.Data.Kernel.Spor.Fi24Net

public section

namespace CFSG.KC.RouteP

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.MonsterConv.Perm CFSG.KC.Fi24Net

@[expose] noncomputable def full : Nat := ones (nat_lit 524288)

@[expose] noncomputable def appP (NW : Nat → Nat → Nat) (z : Int) (v : Nat) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun m => nIf(Nat.beq m (nat_lit 0), v, netF (NW (Nat.sub m (nat_lit 1))) v))
    (fun n => netR (NW n) v) z

@[expose] noncomputable def walkP (NW : Nat → Nat → Nat) (w : List Int) (v : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x) (fun z _ ih x => strictN (appP NW z x) ih) w v

@[expose] noncomputable def lo (c : Nat) : Nat := Nat.land c full

@[expose] noncomputable def hi (c : Nat) : Nat := Nat.shiftRight c (nat_lit 524288)

@[expose] noncomputable def mk (a b : Nat) : Nat := Nat.lor a (Nat.shiftLeft b (nat_lit 524288))

@[expose] noncomputable def zer (a b : Nat) : Nat := Nat.xor full (Nat.land (Nat.lor a b) full)

@[expose] noncomputable def add3a (a0 a1 b0 b1 : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.land (zer a0 a1) b0) (Nat.land a0 (zer b0 b1))) (Nat.land a1 b1)

@[expose] noncomputable def add3b (a0 a1 b0 b1 : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.land (zer a0 a1) b1) (Nat.land a0 b0)) (Nat.land a1 (zer b0 b1))

@[expose] noncomputable def add3 (a0 a1 b0 b1 : Nat) : Nat := mk (add3a a0 a1 b0 b1) (add3b a0 a1 b0 b1)

@[expose] noncomputable def stepK (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (z : Int) (c : Nat) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun m => nIf(Nat.beq m (nat_lit 0), c,
      add3 (netF (NW (Nat.sub m (nat_lit 1))) (lo c)) (netF (NW (Nat.sub m (nat_lit 1))) (hi c))
        (KA (Nat.sub m (nat_lit 1))) (KB (Nat.sub m (nat_lit 1)))))
    (fun n => mk (netR (NW n) (add3a (lo c) (hi c) (KB n) (KA n)))
      (netR (NW n) (add3b (lo c) (hi c) (KB n) (KA n)))) z

@[expose] noncomputable def walkK (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (w : List Int) (c : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun z _ ih x => strictN (stepK NW KA KB z x) ih) w c

@[expose] noncomputable def wordOK (NW : Nat → Nat → Nat) (w : List Int) (j k : Nat) : Bool :=
  letB (tpl k) (fun v => Nat.beq (walkP NW w v) (netF (NW j) v))

@[expose] noncomputable def wordKOK (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (w : List Int) (j : Nat) :
    Bool :=
  Nat.beq (walkK NW KA KB w (nat_lit 0)) (mk (KA j) (KB j))

@[expose] noncomputable def idOK (NW : Nat → Nat → Nat) (w : List Int) (k : Nat) : Bool :=
  letB (tpl k) (fun v => Nat.beq (walkP NW w v) v)

@[expose] noncomputable def idKOK (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (w : List Int) : Bool :=
  Nat.beq (walkK NW KA KB w (nat_lit 0)) (nat_lit 0)

@[expose] noncomputable def kapOK (KA KB : Nat → Nat) (j : Nat) : Bool :=
  andB (Nat.beq (Nat.land (KA j) (KB j)) (nat_lit 0))
    (andB (Nat.beq (Nat.shiftRight (KA j) (nat_lit 306936)) (nat_lit 0))
      (Nat.beq (Nat.shiftRight (KB j) (nat_lit 306936)) (nat_lit 0)))

@[expose] noncomputable def sh (s i : Nat) : Nat :=
  Nat.land (Nat.shiftRight s (Nat.mul i (nat_lit 524288))) full

@[expose] noncomputable def mk3 (a b c : Nat) : Nat :=
  Nat.lor a (Nat.lor (Nat.shiftLeft b (nat_lit 524288)) (Nat.shiftLeft c (nat_lit 1048576)))

@[expose] noncomputable def rotS (a b s0 s1 s2 : Nat) : Nat :=
  mk3 (Nat.lor (Nat.lor (Nat.land (zer a b) s0) (Nat.land a s2)) (Nat.land b s1))
    (Nat.lor (Nat.lor (Nat.land (zer a b) s1) (Nat.land a s0)) (Nat.land b s2))
    (Nat.lor (Nat.lor (Nat.land (zer a b) s2) (Nat.land a s1)) (Nat.land b s0))

@[expose] noncomputable def imgS (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (z : Int) (s : Nat) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun m => nIf(Nat.beq m (nat_lit 0), s,
      (fun j => (fun r => mk3 (netR (NW j) (sh r 0)) (netR (NW j) (sh r 1)) (netR (NW j) (sh r 2)))
        (rotS (KA j) (KB j) (sh s 0) (sh s 1) (sh s 2))) (Nat.sub m (nat_lit 1))))
    (fun n => (fun r => rotS (KB n) (KA n) (sh r 0) (sh r 1) (sh r 2))
      (mk3 (netF (NW n) (sh s 0)) (netF (NW n) (sh s 1)) (netF (NW n) (sh s 2)))) z

@[expose] noncomputable def imgW (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (w : List Int) (s : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) s (fun z _ ih => strictN ih (imgS NW KA KB z)) w

@[expose] noncomputable def single (x : Nat) : Nat :=
  Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.mul (Nat.mod x (nat_lit 3)) (nat_lit 524288)) (Nat.div x (nat_lit 3)))

@[expose] noncomputable def ptOK (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (w : List Int) (x y : Nat) : Bool :=
  Nat.beq (imgW NW KA KB w (single x)) (single y)

@[expose] noncomputable def kapLinkOK (OT : Nat → Nat) (K b : Nat) : Bool :=
  allBelow (nat_lit 600) (nat_lit 10) (fun c => Nat.beq (blk K c)
    (Nat.land (rawPlane (OT c) (nat_lit 64) (nat_lit 512) (nat_lit 9) (nat_lit 0) b)
      (nIf(Nat.blt c (nat_lit 599), ones (nat_lit 512), ones (nat_lit 248)))))

@[expose] noncomputable def roundS (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (gens : List Int) (s : Nat) :
    Nat :=
  List.rec (motive := fun _ => Nat) s
    (fun z _ ih => strictN ih (fun t => Nat.lor t (imgS NW KA KB z s))) gens

@[expose] noncomputable def closeS (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (gens : List Int) (n s : Nat) :
    Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun _ ih x => strictN (roundS NW KA KB gens x) ih) n s

@[expose] noncomputable def closedS (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (gens : List Int) (s : Nat) :
    Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun z _ ih => andB (Nat.beq (imgS NW KA KB z s) s) ih) gens

@[expose] noncomputable def pc64 (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add acc (Nat.land (Nat.shiftRight x i) (nat_lit 1))) (nat_lit 64)

@[expose] noncomputable def pcount (s : Nat) : Nat :=
  sumBelow (nat_lit 24576) (nat_lit 384)
    (fun c => pc64 (fld(s, Nat.mul c (nat_lit 64), nat_lit 18446744073709551615)))

@[expose] noncomputable def ptsS : Nat :=
  mk3 (ones (nat_lit 306936)) (ones (nat_lit 306936)) (ones (nat_lit 306936))

@[expose] noncomputable def orbOK (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (gens : List Int) (x n m : Nat) :
    Bool :=
  letB (closeS NW KA KB gens n (single x)) (fun S =>
    andB (closedS NW KA KB gens S) (Nat.beq (pcount (Nat.land S ptsS)) m))

end CFSG.KC.RouteP

end
