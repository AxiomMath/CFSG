module

public import CFSG.Certificates.Kernel.Orders.Mat
public import CFSG.Certificates.Kernel.Local.LargeCore.Grp

public section

namespace CFSG.KC.LyOm

open CFSG.KC.Loop CFSG.KC.LL CFSG.KC.Ord

@[expose] noncomputable def sp1 (x m s : Nat) : Nat :=
  strictN (Nat.land x m) (fun a => Nat.lor (Nat.xor x a) (Nat.shiftLeft a s))

@[expose] noncomputable def spreadB (MS : List Nat) (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x
    (fun i acc => strictN acc (fun a => sp1 a (pickL MS i)
      (Nat.mul (nat_lit 9) (Nat.shiftLeft (nat_lit 1) (Nat.sub (nat_lit 15) i))))) (nat_lit 16)

@[expose] noncomputable def spMask (i : Nat) : Nat :=
  (fun t => Nat.mul
    (Nat.shiftLeft (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 3) (Nat.shiftLeft (nat_lit 1) t)))
      (nat_lit 1)) (Nat.mul (nat_lit 3) (Nat.shiftLeft (nat_lit 1) t)))
    (rep1 (Nat.mul (nat_lit 12) (Nat.shiftLeft (nat_lit 1) (Nat.succ t)))
      (Nat.shiftLeft (nat_lit 1) (Nat.sub (nat_lit 15) t))))
  (Nat.sub (nat_lit 15) i)

@[expose] noncomputable def spMasksOK (MS : List Nat) : Bool :=
  bAnd(Nat.beq (List.length MS) (nat_lit 16),
    Nat.rec (motive := fun _ => Bool) true
      (fun i ih => bAnd(Nat.beq (pickL MS i) (spMask i), ih)) (nat_lit 16))

structure Consts where
  Lh : Nat
  Hh : Nat
  CMh : Nat
  L7 : Nat
  H7 : Nat
  CM7 : Nat
  ONE7 : Nat
  MASK7 : Nat
  MS : List Nat

@[expose] noncomputable def constsOK (C : Consts) : Bool :=
  bAnd(Nat.beq C.Lh (rep1 (nat_lit 12) (nat_lit 49728)),
  bAnd(Nat.beq C.Hh (Nat.shiftLeft C.Lh (nat_lit 11)),
  bAnd(Nat.beq C.CMh (Nat.mul (nat_lit 4095) (rep1 (nat_lit 1332) (nat_lit 448))),
  bAnd(Nat.beq C.L7 (rep1 (nat_lit 12) (nat_lit 777)),
  bAnd(Nat.beq C.H7 (Nat.shiftLeft C.L7 (nat_lit 11)),
  bAnd(Nat.beq C.CM7 (Nat.mul (nat_lit 4095) (rep1 (nat_lit 1332) (nat_lit 7))),
  bAnd(Nat.beq C.ONE7 (rep1 (nat_lit 1344) (nat_lit 7)),
  bAnd(Nat.beq C.MASK7 (Nat.mul (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 84)) (nat_lit 1))
      (rep1 (nat_lit 1332) (nat_lit 7))),
    spMasksOK C.MS))))))))

@[expose] noncomputable def mulH (C : Consts) (X G : Nat) : Nat :=
  rowsMulR (nat_lit 5) (nat_lit 12) (nat_lit 1332) (nat_lit 37) (nat_lit 3) (nat_lit 8) C.Lh C.Hh
    C.CMh (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1332)) (nat_lit 1)) X G

@[expose] noncomputable def mul7 (C : Consts) (M N : Nat) : Nat :=
  mulR (nat_lit 5) (nat_lit 12) (nat_lit 1332) (nat_lit 7) (nat_lit 8) C.L7 C.H7 C.CM7
    (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1332)) (nat_lit 1)) M N

@[expose] noncomputable def rows7 (Y q : Nat) : Nat :=
  rowsOf (nat_lit 1332) (Nat.mul (nat_lit 7) q) (nat_lit 7) Y

@[expose] noncomputable def isChild (n i : Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) i, Nat.blt i n)

@[expose] noncomputable def gather (KX PT : Nat → Nat) (n b s : Nat) : Nat :=
  strictN (PT b) (fun P =>
    Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun acc _ => acc)
      (fun k ih acc cnt =>
        (fun r => strictN (fldW P (Nat.mul (nat_lit 21) r) (nat_lit 21)) (fun e =>
          nIf(bAnd(isChild n (Nat.add (Nat.shiftLeft b (nat_lit 6)) r),
              Nat.beq (Nat.shiftRight e (nat_lit 20)) s),
            ih (Nat.lor acc (Nat.shiftLeft (getRec KX (nat_lit 2331) (Nat.land e (nat_lit 1048575)))
              (Nat.mul (nat_lit 2331) cnt))) (Nat.succ cnt),
            ih acc cnt)))
        (Nat.sub (nat_lit 63) k))
      (nat_lit 64) (nat_lit 0) (nat_lit 0))

@[expose] noncomputable def leafCmp (C : Consts) (PT : Nat → Nat) (n b Y0 Y1 XC : Nat) : Bool :=
  letB (PT b) (fun P => letB (Nat.shiftLeft b (nat_lit 6)) (fun lo =>
    Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
      (fun k ih c0 c1 =>
        (fun r => letB (fldW P (Nat.mul (nat_lit 21) r) (nat_lit 21)) (fun e =>
          letB (Nat.add lo r) (fun i =>
          bIf(isChild n i,
            letB (rows7 XC r) (fun N =>
            bAnd(Nat.blt (Nat.land e (nat_lit 1048575)) i,
            bAnd(Nat.beq (Nat.land N C.MASK7) C.ONE7,
              bIf(Nat.beq (Nat.shiftRight e (nat_lit 20)) (nat_lit 0),
                letB (rows7 Y0 c0) (fun Y => bAnd(Nat.beq (mul7 C Y N) Y, ih (Nat.succ c0) c1)),
                letB (rows7 Y1 c1) (fun Y => bAnd(Nat.beq (mul7 C Y N) Y, ih c0 (Nat.succ c1))))))),
            ih c0 c1))))
        (Nat.sub (nat_lit 63) k))
      (nat_lit 64) (nat_lit 0) (nat_lit 0)))

@[expose] noncomputable def treeLeaf (C : Consts) (KX PT : Nat → Nat) (G0 G1 n b : Nat) : Bool :=
  letB (gather KX PT n b (nat_lit 0)) (fun P0 => letB (spreadB C.MS P0) (fun X0 =>
  letB (mulH C X0 G0) (fun Y0 =>
  letB (gather KX PT n b (nat_lit 1)) (fun P1 => letB (spreadB C.MS P1) (fun X1 =>
  letB (mulH C X1 G1) (fun Y1 =>
  letB (KX b) (fun K => letB (spreadB C.MS K) (fun XC => leafCmp C PT n b Y0 Y1 XC))))))))

@[expose] noncomputable def treeRange (C : Consts) (KX PT : Nat → Nat) (G0 G1 n b₀ c : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun j ih => bAnd(treeLeaf C KX PT G0 G1 n (Nat.add b₀ j), ih)) c

@[expose] noncomputable def sortChunk (KX SG : Nat → Nat) (n k₀ c : Nat) : Bool :=
  allBelow c (Nat.add (Nat.shiftRight c (nat_lit 6)) (nat_lit 1)) (fun j =>
    (fun k => letB (getRec SG (nat_lit 20) k) (fun a =>
        letB (getRec SG (nat_lit 20) (Nat.succ k)) (fun b =>
          bAnd(Nat.blt a n, bAnd(Nat.blt b n,
            Nat.blt (getRec KX (nat_lit 2331) a) (getRec KX (nat_lit 2331) b))))))
      (Nat.add k₀ j))

end CFSG.KC.LyOm

end
