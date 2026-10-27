module

public import Certificates.Data.Kernel.SporSch.HNXPtL

public section

namespace CFSG.KC.LL.HNX

open CFSG.KC.Loop CFSG.KC.LL

@[expose] noncomputable def fldPack (L RB o c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun r acc => Nat.lor acc (Nat.shiftLeft (fldW L (Nat.add (Nat.mul RB r) o) (nat_lit 21))
      (Nat.mul (nat_lit 21) r))) c

@[expose] noncomputable def imgLeaf (T U : Nat → Nat) (CM3 M G GI o b : Nat) : Bool :=
  letB (CFSG.KS.SporSch.hnxC b) (fun c => letB (U b) (fun L =>
    Nat.beq (mulC CM3 (listA T M (packF (fun x => x) (Nat.mul (nat_lit 64) b) c) c) G)
      (mulC CM3 (listA T M (fldPack L (nat_lit 76) o c) c) GI)))

@[expose] noncomputable def imgRange (T U : Nat → Nat) (CM3 M G GI o lo c : Nat) : Bool :=
  CFSG.KC.Enum.allN c (fun j => imgLeaf T U CM3 M G GI o (Nat.add lo j))

@[expose] noncomputable def eqLeaf (T U : Nat → Nat) (b : Nat) : Bool :=
  letB (T b) (fun L => letB (U b) (fun V => Nat.rec (motive := fun _ => Bool) true
    (fun r ih => bAnd(Nat.beq (fldW V (Nat.mul (nat_lit 76) r) (nat_lit 21))
      (fldW L (Nat.add (Nat.mul (nat_lit 464) r) (nat_lit 399)) (nat_lit 21)), ih))
    (CFSG.KS.SporSch.hnxC b)))

@[expose] noncomputable def eqRange (T U : Nat → Nat) (lo c : Nat) : Bool :=
  CFSG.KC.Enum.allN c (fun j => eqLeaf T U (Nat.add lo j))

@[expose] noncomputable def labOf (U : Nat → Nat) (x : Nat) : Nat :=
  fldW (getRec U (nat_lit 76) x) (nat_lit 42) (nat_lit 4)

@[expose] noncomputable def orbRec (U : Nat → Nat) (REPS i rec : Nat) : Bool :=
  letB (fldW rec (nat_lit 0) (nat_lit 21)) (fun u1 =>
  letB (fldW rec (nat_lit 21) (nat_lit 21)) (fun u2 =>
  letB (fldW rec (nat_lit 42) (nat_lit 4)) (fun lab =>
  letB (fldW rec (nat_lit 46) (nat_lit 8)) (fun d =>
  letB (fldW REPS (Nat.mul (nat_lit 21) lab) (nat_lit 21)) (fun rp =>
  bAnd(Nat.blt u1 (nat_lit 1140000), bAnd(Nat.blt u2 (nat_lit 1140000), bAnd(Nat.blt lab (nat_lit 12),
  bAnd(Nat.beq (labOf U u1) lab, bAnd(Nat.beq (labOf U u2) lab, bAnd(Nat.ble rp i,
  bIf(Nat.beq d (nat_lit 0), Nat.beq i rp,
    letB (fldW rec (nat_lit 54) (nat_lit 21)) (fun p => bAnd(Nat.blt p (nat_lit 1140000),
      letB (getRec U (nat_lit 76) p) (fun q =>
        bAnd(Nat.beq (Nat.succ (fldW q (nat_lit 46) (nat_lit 8))) d,
          Nat.beq (fldW q (Nat.mul (nat_lit 21) (fldW rec (nat_lit 75) (nat_lit 1))) (nat_lit 21)) i))))))))))))))))

@[expose] noncomputable def orbLeaf (U : Nat → Nat) (REPS b : Nat) : Bool :=
  letB (U b) (fun L => Nat.rec (motive := fun _ => Bool) true
    (fun r ih => bAnd(orbRec U REPS (Nat.add (Nat.mul (nat_lit 64) b) r)
      (fldW L (Nat.mul (nat_lit 76) r) (nat_lit 76)), ih)) (CFSG.KS.SporSch.hnxC b))

@[expose] noncomputable def orbRange (U : Nat → Nat) (REPS lo c : Nat) : Bool :=
  CFSG.KC.Enum.allN c (fun j => orbLeaf U REPS (Nat.add lo j))

@[expose] noncomputable def cntLeaf (U : Nat → Nat) (b : Nat) : Nat :=
  strictN (U b) (fun L => Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun r acc => Nat.add acc (Nat.shiftLeft (nat_lit 1)
      (Nat.mul (nat_lit 21) (fldW L (Nat.add (Nat.mul (nat_lit 76) r) (nat_lit 42)) (nat_lit 4)))))
    (CFSG.KS.SporSch.hnxC b))

@[expose] noncomputable def cntSum (U : Nat → Nat) (lo c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => strictN acc (fun a => Nat.add a (cntLeaf U (Nat.add lo j)))) c

end CFSG.KC.LL.HNX

end
