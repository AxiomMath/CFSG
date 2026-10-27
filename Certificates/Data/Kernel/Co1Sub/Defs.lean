module

public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.Kernel.F2Word

public section

namespace CFSG.KC.Co1Sub

open CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.F2W CFSG.KLie.CT

@[expose] noncomputable def mulS (A B : Nat) : Nat := mulW (nat_lit 24) A B

@[expose] noncomputable def oneS : Nat := idF (nat_lit 24)

@[expose] noncomputable def vmS (M v : Nat) : Nat := vmF (nat_lit 24) M v

@[expose] noncomputable def entS (nB : Nat) (B M : List Nat) (i : Nat) : Nat :=
  nIf(Nat.blt i nB, getL (nat_lit 0) B i, getL (nat_lit 0) M (Nat.sub i nB))

@[expose] noncomputable def letS (nB : Nat) (B Bi M Mi : List Nat) (c : Nat) : Nat :=
  nIf(bit c (nat_lit 0), entS nB Bi Mi (Nat.shiftRight c (nat_lit 1)),
    entS nB B M (Nat.shiftRight c (nat_lit 1)))

@[expose] noncomputable def wordFromS (nB : Nat) (B Bi M Mi : List Nat) (w : List Nat) :
    Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun c _ ih acc => strictN (mulS acc (letS nB B Bi M Mi c)) ih) w

@[expose] noncomputable def wordS (nB : Nat) (B Bi M Mi : List Nat) (w : List Nat) : Nat :=
  wordFromS nB B Bi M Mi w oneS

@[expose] noncomputable def refsK (lim : Nat) (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun c _ ih => andB (Nat.blt (Nat.shiftRight c (nat_lit 1)) lim) ih) w

@[expose] noncomputable def slpAt (nB : Nat) (B Bi M Mi : List Nat) (W : List (List Nat)) :
    Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool)
    (fun j => andB (Nat.beq (lenL M) j) (Nat.beq (lenL Mi) j))
    (fun w _ ih j => strictB j fun j => andB (refsK (Nat.add nB j) w) (andB
      (Nat.beq (getL (nat_lit 0) M j) (wordS nB B Bi M Mi w))
      (andB (Nat.beq (mulS (getL (nat_lit 0) M j) (getL (nat_lit 0) Mi j)) oneS)
        (ih (Nat.succ j))))) W

@[expose] noncomputable def slpK (B Bi : List Nat) (W : List (List Nat)) (M Mi : List Nat) : Bool :=
  strictB (lenL B) fun nB => slpAt nB B Bi M Mi W (nat_lit 0)

@[expose] noncomputable def invsK (B : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun l => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l)
    (fun m _ ih l => List.rec (motive := fun _ => Bool) false
      (fun mi t _ => andB (Nat.beq (mulS m mi) oneS) (ih t)) l) B

@[expose] noncomputable def pickL (L : List Nat) (idx : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun i _ ih => List.cons (getL (nat_lit 0) L i) ih)
    idx

@[expose] noncomputable def recT (C : List Nat) (k : Nat) : Nat :=
  fld(getL (nat_lit 0) C (Nat.shiftRight k (nat_lit 8)),
    Nat.mul (Nat.land k (nat_lit 255)) (nat_lit 64), nat_lit 18446744073709551615)

@[expose] noncomputable def ptT (r : Nat) : Nat := Nat.land r (nat_lit 16777215)

@[expose] noncomputable def parT (r : Nat) : Nat := fld(r, nat_lit 24, nat_lit 65535)

@[expose] noncomputable def genT (r : Nat) : Nat := fld(r, nat_lit 40, nat_lit 255)

@[expose] noncomputable def depT (r : Nat) : Nat := fld(r, nat_lit 48, nat_lit 65535)

@[expose] noncomputable def treeAt (gens : List Nat) (x0 N : Nat) (C : List Nat) (k : Nat) : Bool :=
  strictB (recT C k) fun r => andB
    (bIf(Nat.blt (Nat.succ k) N, Nat.blt (ptT r) (ptT (recT C (Nat.succ k))), true))
    (bIf(Nat.beq (depT r) (nat_lit 0), Nat.beq (ptT r) x0,
      strictB (parT r) fun p => strictB (recT C p) fun q => andB (Nat.blt p N) (andB
        (Nat.blt (genT r) (lenL gens)) (andB (Nat.beq (Nat.succ (depT q)) (depT r))
          (Nat.beq (vmS (getL (nat_lit 0) gens (genT r)) (ptT q)) (ptT r))))))

@[expose] noncomputable def treeK (gens : List Nat) (x0 N : Nat) (C : List Nat) : Bool :=
  allBelow N (Nat.succ (Nat.shiftRight N (nat_lit 6))) (treeAt gens x0 N C)

@[expose] noncomputable def fixK (gens : List Nat) (x : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun g _ ih => andB (Nat.beq (vmS g x) x) ih) gens

@[expose] noncomputable def upM : Nat :=
  orN (nat_lit 24) fun i =>
    Nat.shiftLeft (Nat.sub (maskN (nat_lit 24)) (maskN i)) (Nat.mul (nat_lit 24) i)

@[expose] noncomputable def lutK (U : Nat) : Bool := Nat.beq (Nat.land U upM) oneS

@[expose] noncomputable def redK (b v : Nat) : Nat :=
  nIf(Nat.beq (Nat.land v (Nat.sub b (Nat.land b (Nat.sub b (nat_lit 1))))) (nat_lit 0), v,
    Nat.xor v b)

@[expose] noncomputable def key4 (Q : Nat) : Nat :=
  strictN (fget Q (nat_lit 0) (nat_lit 24)) fun c0 =>
  strictN (redK c0 (fget Q (nat_lit 1) (nat_lit 24))) fun c1 =>
  strictN (redK c1 (redK c0 (fget Q (nat_lit 2) (nat_lit 24)))) fun c2 =>
  strictN (redK c2 (redK c1 (redK c0 (fget Q (nat_lit 3) (nat_lit 24))))) fun c3 =>
    Nat.lor (Nat.lor c0 (Nat.shiftLeft c1 (nat_lit 24)))
      (Nat.lor (Nat.shiftLeft c2 (nat_lit 48)) (Nat.shiftLeft c3 (nat_lit 72)))

@[expose] noncomputable def imgF (r t : Nat) : Nat := fld(r, Nat.mul (nat_lit 16) t, nat_lit 65535)

@[expose] noncomputable def parF (r : Nat) : Nat := fld(r, nat_lit 128, nat_lit 65535)

@[expose] noncomputable def genF (r : Nat) : Nat := fld(r, nat_lit 144, nat_lit 255)

@[expose] noncomputable def depF (r : Nat) : Nat := fld(r, nat_lit 152, nat_lit 65535)

@[expose] noncomputable def flagAt (gens : List Nat) (P0 : Nat) (P Pi R : List Nat) (N k : Nat) :
    Bool :=
  strictB (getL (nat_lit 0) P k) fun Q => strictB (getL (nat_lit 0) R k) fun r =>
    andB (Nat.beq (mulS Q (getL (nat_lit 0) Pi k)) oneS) (andB
      (allN (lenL gens) fun t => strictB (imgF r t) fun j => andB (Nat.blt j N)
        (lutK (mulS (mulS Q (getL (nat_lit 0) gens t)) (getL (nat_lit 0) Pi j))))
      (andB (bIf(Nat.blt (Nat.succ k) N, Nat.blt (key4 Q) (key4 (getL (nat_lit 0) P (Nat.succ k))),
          true))
        (bIf(Nat.beq (depF r) (nat_lit 0), Nat.beq Q P0,
          strictB (parF r) fun p => strictB (getL (nat_lit 0) R p) fun q => andB (Nat.blt p N)
            (andB (Nat.blt (genF r) (lenL gens)) (andB (Nat.beq (Nat.succ (depF q)) (depF r))
              (Nat.beq (imgF q (genF r)) k)))))))

@[expose] noncomputable def flagK (gens : List Nat) (P0 : Nat) (P Pi R : List Nat) : Bool :=
  strictB (lenL P) fun N => andB (Nat.beq (lenL Pi) N) (andB (Nat.beq (lenL R) N)
    (allBelow N (Nat.succ (Nat.shiftRight N (nat_lit 6))) (flagAt gens P0 P Pi R N)))

end CFSG.KC.Co1Sub

end
