module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.Syl2072

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def bp (t : Nat) : Nat :=
  fld(nat_lit 0x4006003002001000, Nat.mul (nat_lit 12) t, nat_lit 4095)

@[expose] noncomputable def ap (q y : Nat) : Nat := pg (nat_lit 12) (mask (nat_lit 12)) q y

@[expose] noncomputable def bim (v t : Nat) : Nat := fld(v, Nat.mul (nat_lit 12) t, nat_lit 4095)

@[expose] noncomputable def f16 (v k : Nat) : Nat :=
  fld(v, Nat.add (nat_lit 72) (Nat.mul (nat_lit 16) k), nat_lit 65535)

@[expose] noncomputable def key (v : Nat) : Nat := fld(v, nat_lit 0, nat_lit 4722366482869645213695)

@[expose] noncomputable def iter (F : Nat → Nat) (k y : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) y (fun _ ih => strictN ih F) k

@[expose] noncomputable def walk (L D : Nat → Nat) (s0 o f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ y => y)
    (fun _ ih i y => strictN (D (Nat.add o i)) fun v =>
      strictN (ih (f16 v (nat_lit 0)) y) fun z => ap (L (Nat.add s0 (f16 v (nat_lit 1)))) z) f

@[expose] noncomputable def act (L D : Nat → Nat) (s0 o i y : Nat) : Nat :=
  walk L D s0 o (f16 (D (Nat.add o i)) (nat_lit 2)) i y

@[expose] noncomputable def all6 (P : Nat → Bool) : Bool := allN (nat_lit 6) P

@[expose] noncomputable def treeK (L D : Nat → Nat) (s0 m o n v : Nat) : Bool :=
  bIf(Nat.beq (f16 v (nat_lit 2)) (nat_lit 0),
    all6 fun t => Nat.beq (bim v t) (bp t),
    strictB (f16 v (nat_lit 0)) fun par => strictB (f16 v (nat_lit 1)) fun lab =>
      strictB (D (Nat.add o par)) fun u =>
        bAnd(Nat.blt par n, bAnd(Nat.blt lab m,
          bAnd(Nat.beq (Nat.succ (f16 u (nat_lit 2))) (f16 v (nat_lit 2)),
            all6 fun t => Nat.beq (bim v t) (ap (L (Nat.add s0 lab)) (bim u t))))))

@[expose] noncomputable def nxtK (L D : Nat → Nat) (s0 m o n v : Nat) : Bool :=
  allN m fun k => strictB (f16 v (Nat.add (nat_lit 6) k)) fun j =>
    strictB (D (Nat.add o j)) fun u => bAnd(Nat.blt j n,
      all6 fun t => Nat.beq (ap (L (Nat.add s0 k)) (bim v t)) (bim u t))

@[expose] noncomputable def covK (L D X : Nat → Nat) (s0 o n p nw i v : Nat) : Bool :=
  strictB (f16 v (nat_lit 3)) fun w => strictB (f16 v (nat_lit 4)) fun t =>
    strictB (f16 v (nat_lit 5)) fun j => strictB (D (Nat.add o t)) fun u =>
      bAnd(Nat.blt w nw, bAnd(Nat.blt t n, bAnd(Nat.blt (nat_lit 0) j, bAnd(Nat.blt j p,
        all6 fun b => Nat.beq (act L D s0 o i (bim u b))
          (act L D s0 o t (iter (ap (X w)) j (bp b)))))))

@[expose] noncomputable def elemK (L D X : Nat → Nat) (s0 m o n p nw i : Nat) : Bool :=
  strictB (D (Nat.add o i)) fun v =>
    bAnd(treeK L D s0 m o n v, bAnd(nxtK L D s0 m o n v,
      bAnd(bIf(Nat.blt (Nat.succ i) n, Nat.blt (key v) (key (D (Nat.add o (Nat.succ i)))), true),
        bIf(bAnd(all6 fun t => Nat.beq (iter (act L D s0 o i) p (bp t)) (bp t),
            Bool.not (all6 fun t => Nat.beq (bim v t) (bp t))),
          covK L D X s0 o n p nw i v, true))))

@[expose] noncomputable def recK (L D X : Nat → Nat) (s0 m o n p nw r : Nat) : Bool :=
  bAnd(Nat.blt r n, bAnd(Nat.beq (f16 (D (Nat.add o r)) (nat_lit 2)) (nat_lit 0),
    allN n (elemK L D X s0 m o n p nw)))

@[expose] noncomputable def witK (x h hi p o : Nat) : Bool :=
  bAnd(Bool.not (all6 fun t => Nat.beq (ap x (bp t)) (bp t)),
    bAnd(all6 fun t => Nat.beq (iter (ap x) p (bp t)) (bp t),
      bAnd(Nat.beq (Nat.mod o (nat_lit 2)) (nat_lit 0),
        bAnd(all6 fun t => Nat.beq (iter (fun z => ap x (ap h (ap x (ap hi z)))) o (bp t)) (bp t),
          Bool.not (all6 fun t =>
            Nat.beq (iter (fun z => ap x (ap h (ap x (ap hi z)))) (Nat.div o (nat_lit 2)) (bp t))
              (bp t))))))

end CFSG.KC.Syl2072

end
