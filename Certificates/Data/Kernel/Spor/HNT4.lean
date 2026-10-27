module

public import Certificates.Data.Kernel.Spor.Chain
public import Certificates.Data.Kernel.Spor.BaseEq
public import Certificates.Data.Kernel.Spor.HNAOrb

public section

namespace CFSG.KS.HNT4

open CFSG.KC.Enum CFSG.KS CFSG.KS.BaseEq CFSG.KS.HNA

@[expose] noncomputable def t4Len (WN : Nat → Nat) (s : Nat) : Nat :=
  strictN (WN s) fun c =>
    nIf(Nat.beq c (nat_lit 0), nat_lit 1,
      nIf(Nat.beq c (nat_lit 1), Nat.add (nat_lit 3) (WN (Nat.succ s)),
        nIf(Nat.beq c (nat_lit 2), nat_lit 3, nat_lit 2)))

@[expose] noncomputable def t4PosK (WN P : Nat → Nat) (N K : Nat) : Bool :=
  bAnd(Nat.beq (P (nat_lit 0)) (nat_lit 0), bAnd(Nat.beq (P K) N,
    allN K fun j => Nat.beq (P (Nat.succ j)) (Nat.add (P j) (t4Len WN (P j)))))

@[expose] noncomputable def poolLen (WN : Nat → Nat) (s : Nat) : Nat :=
  strictN (WN s) fun l1 => Nat.add (Nat.add (nat_lit 2) l1) (WN (Nat.add (Nat.succ s) l1))

@[expose] noncomputable def poolPosK (WN P : Nat → Nat) (N K : Nat) : Bool :=
  bAnd(Nat.beq (P (nat_lit 0)) (nat_lit 0), bAnd(Nat.beq (P K) N,
    allN K fun j => Nat.beq (P (Nat.succ j)) (Nat.add (P j) (poolLen WN (P j)))))

@[expose] noncomputable def wordAt (WN : Nat → Nat) (s L : Nat) : List Int :=
  (listUp (fun t => WN (Nat.add s t)) L).map fun x => Int.subNatNat x (nat_lit 11)

@[expose] noncomputable def invWK (w : List Int) : List Int := (w.map Int.neg).reverse

@[expose] noncomputable def poolComm (WN : Nat → Nat) (s : Nat) : List Int :=
  (fun u v => u ++ v ++ invWK u ++ invWK v) (wordAt WN (Nat.succ s) (WN s))
    (wordAt WN (Nat.add (Nat.add s (nat_lit 2)) (WN s)) (WN (Nat.add (Nat.succ s) (WN s))))

@[expose] noncomputable def letsK (WN : Nat → Nat) (s L : Nat) : Bool :=
  allL (listUp (fun t => WN (Nat.add s t)) L) fun x =>
    bAnd(Nat.blt (nat_lit 11) x, Nat.blt x (nat_lit 22))

@[expose] noncomputable def poolLetK (WN : Nat → Nat) (s : Nat) : Bool :=
  strictB (WN s) fun l1 => bAnd(letsK WN (Nat.succ s) l1,
    letsK WN (Nat.add (Nat.add s (nat_lit 2)) l1) (WN (Nat.add (Nat.succ s) l1)))

@[expose] noncomputable def zP (e a b : Nat) : Nat :=
  pcomp (nat_lit 800) (nat_lit 10) (mask 10) (pcomp (nat_lit 800) (nat_lit 10) (mask 10) e a)
    (pcomp (nat_lit 800) (nat_lit 10) (mask 10) e b)

@[expose] noncomputable def prodL (I : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) I
    (fun a _ ih => strictN ih fun q => pcomp (nat_lit 800) (nat_lit 10) (mask 10) a q) l

@[expose] noncomputable def t4WK (ps : List Nat) (WN P T CP CQ : Nat → Nat) (I nc k : Nat) : Bool :=
  strictB (P k) fun s => strictB (WN s) fun c =>
    bIf(Nat.beq c (nat_lit 0),
      bIf(Nat.beq k (nat_lit 0), true, Bool.not (sqFixK (nat_lit 10) (mask 10) ps (T k))),
    bIf(Nat.beq c (nat_lit 1),
      strictB (WN (Nat.succ s)) fun L =>
        bAnd(allL (listUp (fun t => WN (Nat.add (Nat.add s (nat_lit 2)) t)) L)
            (fun f => Nat.blt f nc),
          strictB (T k) fun e =>
            ord4K (nat_lit 800) (nat_lit 10) I (ppow (nat_lit 800) (nat_lit 10) (mask 10) I
              (prodL I ((listUp (fun t => WN (Nat.add (Nat.add s (nat_lit 2)) t)) L).map
                fun f => zP e (CP f) (CQ f)))
              (WN (Nat.add (Nat.add s (nat_lit 2)) L)))),
    bIf(Nat.beq c (nat_lit 2),
      strictB (WN (Nat.succ s)) fun f =>
        bAnd(Nat.blt f nc, bAnd(Nat.blt (WN (Nat.add s (nat_lit 2))) (nat_lit 1140000),
          strictB (zP (T k) (CP f) (CQ f)) fun z =>
            Nat.beq (pcomp (nat_lit 800) (nat_lit 10) (mask 10) z z) I)),
    bIf(Nat.beq c (nat_lit 3), Nat.blt (WN (Nat.succ s)) (nat_lit 1140000), false))))

end CFSG.KS.HNT4

end
