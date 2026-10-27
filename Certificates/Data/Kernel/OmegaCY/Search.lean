module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.OmegaCY

@[expose] noncomputable def bt (a i : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight a i) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def lane (c i : Nat) : Nat :=
  Nat.land (Nat.shiftRight c (Nat.mul (nat_lit 7) i)) (nat_lit 127)

@[expose] noncomputable def cg (tab i j : Nat) : Nat :=
  Nat.land (Nat.shiftRight tab
    (Nat.mul (nat_lit 3) (Nat.add (Nat.div (Nat.mul i (Nat.sub i (nat_lit 1))) (nat_lit 2)) j)))
    (nat_lit 7)

@[expose] noncomputable def bfT (tab a b i j o : Nat) : Nat :=
  nIf(bAnd(bt a i, bt b j), Nat.land (Nat.shiftRight tab o) (nat_lit 7), nat_lit 0)

@[expose] noncomputable def bf (tab a b : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (bfT tab a b (nat_lit 4) (nat_lit 3) (nat_lit 27))
      (bfT tab a b (nat_lit 5) (nat_lit 3) (nat_lit 39)))
    (Nat.xor (bfT tab a b (nat_lit 6) (nat_lit 3) (nat_lit 54))
      (bfT tab a b (nat_lit 5) (nat_lit 4) (nat_lit 42))))
    (Nat.xor (bfT tab a b (nat_lit 6) (nat_lit 4) (nat_lit 57))
      (bfT tab a b (nat_lit 6) (nat_lit 5) (nat_lit 60)))

@[expose] noncomputable def bm2 (tab a b : Nat) : Nat := Nat.xor (Nat.xor a b) (bf tab a b)

@[expose] noncomputable def tabOK (tab : Nat) : Bool :=
  Nat.beq (Nat.lor tab (nat_lit 7890336234772365312)) (nat_lit 7890336234772365312)

@[expose] noncomputable def beta2 (tab c k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i r => nIf(bt k i, bm2 tab r (lane c i), r)) (nat_lit 7)

@[expose] noncomputable def cen (c w : Nat) : Nat :=
  Nat.xor (Nat.xor (nIf(bt w (nat_lit 0), lane c (nat_lit 0), nat_lit 0))
    (nIf(bt w (nat_lit 1), lane c (nat_lit 1), nat_lit 0)))
    (nIf(bt w (nat_lit 2), lane c (nat_lit 2), nat_lit 0))

@[expose] noncomputable def allR (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i r => bAnd(f i, r)) n

@[expose] noncomputable def anyR (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i r => bIf(f i, true, r)) n

@[expose] noncomputable def relK (tab c v w e : Nat) : Bool :=
  Nat.beq (Nat.xor (bf tab v w) (bf tab w v)) (cen c e)

@[expose] noncomputable def stage2 (iv : Bool) (tab m c : Nat) : Bool :=
  (fun v => bAnd(Nat.beq (bf tab v v) (nat_lit 0),
    bAnd(allR (Nat.sub m (nat_lit 1))
        (fun i => relK tab c v (lane c i) (cg tab (Nat.sub m (nat_lit 1)) i)),
      bIf(iv, allR m (fun g => bIf(Nat.ble (Nat.shiftLeft (nat_lit 1) m) (lane c g), true,
        Nat.beq (beta2 tab c (lane c g)) (Nat.shiftLeft (nat_lit 1) g))), true))))
    (lane c (Nat.sub m (nat_lit 1)))

@[expose] noncomputable def goalU (tab k b : Nat) : Bool :=
  (fun u => bAnd(Nat.beq (bm2 tab k u) b, bAnd(Nat.beq (bm2 tab u u) (nat_lit 0),
      bAnd(bIf(Nat.beq u (nat_lit 0), false, true), bIf(Nat.beq u (nat_lit 2), false, true)))))
    (bm2 tab (bm2 tab k (bm2 tab k k)) b)

@[expose] noncomputable def goalK2 (tab c k : Nat) : Bool := goalU tab k (beta2 tab c k)

@[expose] noncomputable def goal2 (tab c : Nat) : Bool :=
  bIf(goalK2 tab c (nat_lit 32), true, bIf(goalK2 tab c (nat_lit 96), true,
    bIf(goalK2 tab c (nat_lit 104), true, anyR (nat_lit 128) (goalK2 tab c))))

@[expose] noncomputable def sp0 (v : Nat) : Nat :=
  Nat.lor (Nat.land v (nat_lit 7))
    (Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight v (nat_lit 3)) (nat_lit 1)) (nat_lit 4))
      (Nat.shiftLeft (Nat.land (Nat.shiftRight v (nat_lit 4)) (nat_lit 1)) (nat_lit 6)))

@[expose] noncomputable def sp2 (v : Nat) : Nat :=
  Nat.lor (Nat.land v (nat_lit 15))
    (Nat.shiftLeft (Nat.land (Nat.shiftRight v (nat_lit 4)) (nat_lit 1)) (nat_lit 5))

@[expose] noncomputable def cand (m v : Nat) : Nat :=
  nIf(Nat.beq m (nat_lit 0), nat_lit 3, nIf(Nat.beq m (nat_lit 1), nat_lit 2,
    nIf(Nat.beq m (nat_lit 2), v,
      nIf(Nat.beq (Nat.land m (nat_lit 1)) (nat_lit 1), sp0 v, sp2 v))))

@[expose] noncomputable def candN (m : Nat) : Nat :=
  nIf(Nat.blt m (nat_lit 2), nat_lit 1, nIf(Nat.beq m (nat_lit 2), nat_lit 8, nat_lit 32))

@[expose] noncomputable def lvl (iv : Bool) (tab : Nat) (ih : Nat → Nat → Bool) (m c : Nat) :
    Bool :=
  bIf(bAnd(Nat.beq m (nat_lit 6), goalK2 tab c (nat_lit 32)), true,
    allR (candN m) (fun v =>
      (fun c' => bIf(stage2 iv tab (Nat.succ m) c', ih (Nat.succ m) c', true))
        (Nat.lor c (Nat.shiftLeft (cand m v) (Nat.mul (nat_lit 7) m)))))

@[expose] noncomputable def srchF (iv : Bool) (tab : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ c => goal2 tab c)
    (fun _ ih m c => lvl iv tab ih m c) (nat_lit 7) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def srch3 (tab : Nat) : Bool := srchF true tab

end CFSG.KC.OmegaCY

end
