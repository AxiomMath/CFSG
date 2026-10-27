module

public import Certificates.Data.Kernel.LyY.Scan

public section

namespace CFSG.KC.LyY

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Child3

@[expose] noncomputable def lgetL (Ls : List (List Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun S _ ih i => Nat.rec (motive := fun _ => List Nat) S (fun j _ => ih j) i) Ls

@[expose] noncomputable def memN (p : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => bIf(Nat.beq x p, true, ih)) l

@[expose] noncomputable def incN (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x xs ih => bAnd(List.rec (motive := fun _ => Bool) true (fun y _ _ => Nat.blt x y) xs, ih)) l

@[expose] noncomputable def allL (f : Nat → Bool) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(f x, ih)) l

@[expose] noncomputable def lenN (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def keyN (w : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ ih => Nat.lor x (Nat.shiftLeft ih w)) l

@[expose] noncomputable def orbOK (n w : Nat) (G : Nat → Nat) (k L : Nat) (TL TP TG TD : List Nat) :
    Bool :=
  allN n (fun p => strictB (lget TL p) (fun l => bAnd(Nat.blt l L,
    bAnd(allN k (fun j => Nat.beq (lget TL (pg w (mask w) (G j) p)) l),
    strictB (lget TP p) (fun q => bIf(Nat.beq q p,
      bAnd(Nat.beq (lget TD p) (nat_lit 0),
        allN p (fun r => bIf(Nat.beq (lget TL r) l, false, true))),
      bAnd(Nat.blt q n, bAnd(Nat.blt (lget TG p) k,
        bAnd(Nat.beq (lget TD p) (Nat.succ (lget TD q)),
          Nat.beq (pg w (mask w) (G (lget TG p)) q) p)))))))))

@[expose] noncomputable def lblCnt (n : Nat) (TL : List Nat) (k : Nat) : Nat :=
  sumF n (fun p => nIf(Nat.beq (lget TL p) k, nat_lit 1, nat_lit 0))

@[expose] noncomputable def imgOK (n w A B : Nat) (TL : List Nat) (k : Nat) (OS : List (List Nat))
    (OP OG : List Nat) (N : Nat) : Bool :=
  bAnd(allL (fun p => Nat.beq (lget TL p) k) (lgetL OS (nat_lit 0)),
    allN N (fun i => bAnd(Nat.beq (lenN (lgetL OS i)) (nat_lit 12), bAnd(incN (lgetL OS i),
      bAnd(allL (fun p => Nat.blt p n) (lgetL OS i), bIf(Nat.beq i (nat_lit 0), true,
        bAnd(Nat.blt (lget OP i) i, bAnd(Nat.blt (lget OG i) (nat_lit 2),
          allL (fun p => memN (pg w (mask w) (nIf(Nat.beq (lget OG i) (nat_lit 0), A, B)) p)
            (lgetL OS i)) (lgetL OS (lget OP i))))))))))

@[expose] noncomputable def distinctOK (w : Nat) (OS : List (List Nat)) (N : Nat) : Bool :=
  allN N (fun i => allN i (fun j =>
    bIf(Nat.beq (keyN w (lgetL OS i)) (keyN w (lgetL OS j)), false, true)))

@[expose] noncomputable def clsKey (n w : Nat) (LR TR TRI : Nat → Nat) (BP X c : Nat) : Nat :=
  strictN (LR (nat_lit 0)) (fun L0 => strictN (LR (nat_lit 1)) (fun L1 =>
  strictN (LR (nat_lit 2)) (fun L2 =>
  strictN (Nat.mod c (rcnt L0)) (fun i => strictN (Nat.mod (Nat.div c (rcnt L0)) (rcnt L1)) (fun j =>
  strictN (Nat.div (Nat.div c (rcnt L0)) (rcnt L1)) (fun k =>
  conjKey w BP X (TR (Nat.add (roff n (Nat.mul n w) L0) i)) (TR (Nat.add (roff n (Nat.mul n w) L1) j))
    (TR (Nat.add (roff n (Nat.mul n w) L2) k)) (TRI (Nat.add (roff n (Nat.mul n w) L0) i))
    (TRI (Nat.add (roff n (Nat.mul n w) L1) j)) (TRI (Nat.add (roff n (Nat.mul n w) L2) k))))))))

@[expose] noncomputable def codeOK (LR : Nat → Nat) (c : Nat) : Bool :=
  Nat.blt c (Nat.mul (rcnt (LR (nat_lit 0))) (Nat.mul (rcnt (LR (nat_lit 1))) (rcnt (LR (nat_lit 2)))))

@[expose] noncomputable def clsOK (n w : Nat) (LR TR TRI : Nat → Nat) (BP X : Nat) (C : List Nat)
    (N : Nat) : Bool :=
  bAnd(Nat.beq (lenN C) N, bAnd(allL (codeOK LR) C,
    allN (Nat.pred N) (fun i => Nat.blt (clsKey n w LR TR TRI BP X (lget C i))
      (clsKey n w LR TR TRI BP X (lget C (Nat.succ i))))))

@[expose] noncomputable def codeProd (n w : Nat) (LR TR : Nat → Nat) (c : Nat) : Nat :=
  strictN (LR (nat_lit 0)) (fun L0 => strictN (LR (nat_lit 1)) (fun L1 =>
  strictN (LR (nat_lit 2)) (fun L2 =>
  pcomp n w (mask w) (TR (Nat.add (roff n (Nat.mul n w) L0) (Nat.mod c (rcnt L0))))
    (pcomp n w (mask w) (TR (Nat.add (roff n (Nat.mul n w) L1) (Nat.mod (Nat.div c (rcnt L0)) (rcnt L1))))
      (TR (Nat.add (roff n (Nat.mul n w) L2) (Nat.div (Nat.div c (rcnt L0)) (rcnt L1))))))))

end CFSG.KC.LyY

end
