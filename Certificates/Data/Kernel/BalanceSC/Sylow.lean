module

public import Certificates.Data.Kernel.BalanceSC.Check
public import Certificates.Data.Kernel.Misc.ArrEnum

public section

namespace CFSG.KC.BalanceSC

open CFSG.KC.Enum (pg pcomp pidn strictB)
open CFSG.KC.LQT.P (allN anyN)

@[expose] noncomputable def getL {α : Type} (d : α) (L : List α) (i : Nat) : α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun x _ ih i => Nat.rec (motive := fun _ => α) x (fun j _ => ih j) i) L i

@[expose] noncomputable def allL (L : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun d _ ih => bAnd(f d, ih)) L

@[expose] noncomputable def movK (n p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add acc (nIf(Nat.beq (pg (nat_lit 4) (nat_lit 15) p i) i, nat_lit 0,
      nat_lit 1))) n

@[expose] noncomputable def invK (n m e p : Nat) : Bool :=
  strictB p fun q =>
    bAnd(Nat.beq (pcomp n (nat_lit 4) (nat_lit 15) q q) e, Nat.beq (movK n q) m)

@[expose] noncomputable def isoK (n e p : Nat) : Bool := invK n (nat_lit 8) e p

@[expose] noncomputable def dblK (n e p : Nat) : Bool := invK n (nat_lit 4) e p

@[expose] noncomputable def commK (n a b : Nat) : Bool :=
  Nat.beq (pcomp n (nat_lit 4) (nat_lit 15) a b) (pcomp n (nat_lit 4) (nat_lit 15) b a)

@[expose] noncomputable def adjK (n e a b : Nat) : Bool :=
  bAnd(notB (Nat.beq a b), bAnd(commK n a b, isoK n e (pcomp n (nat_lit 4) (nat_lit 15) a b)))

@[expose] noncomputable def strictL (y : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def isoIdxK (n N : Nat) (PT : Nat → Nat) : List Nat :=
  strictL (pidn n (nat_lit 4)) fun e => (List.range N).filter fun k => isoK n e (PT k)

@[expose] noncomputable def nbrK (n : Nat) (PT : Nat → Nat) (I : List Nat) : Bool :=
  strictB (pidn n (nat_lit 4)) fun e =>
    allL I fun k => strictB (PT k) fun a => anyL I fun l => strictB (PT l) fun b => adjK n e a b

@[expose] noncomputable def connK (n : Nat) (PT : Nat → Nat) (I ORD : List Nat) : Bool :=
  strictB (pidn n (nat_lit 4)) fun e => strictB I.length fun m =>
    bAnd(Nat.blt (nat_lit 0) m, bAnd(Nat.beq (getL (nat_lit 0) ORD (nat_lit 0)) (nat_lit 0),
      bAnd(allN m (fun i => memL i ORD),
        allN ORD.length fun k => bAnd(Nat.blt (getL (nat_lit 0) ORD k) m,
          bIf(Nat.beq k (nat_lit 0), true, anyN k fun j =>
            strictB (PT (getL (nat_lit 0) I (getL (nat_lit 0) ORD j))) fun a =>
              strictB (PT (getL (nat_lit 0) I (getL (nat_lit 0) ORD k))) fun b =>
                adjK n e a b)))))

@[expose] noncomputable def c2K (n e a b ab : Nat) : Bool := bAnd(commK n a b, isoK n e ab)

@[expose] noncomputable def c3K (n e a b ab c : Nat) : Bool :=
  bAnd(commK n a c, bAnd(commK n b c, bAnd(isoK n e (pcomp n (nat_lit 4) (nat_lit 15) a c),
    bAnd(isoK n e (pcomp n (nat_lit 4) (nat_lit 15) b c),
      isoK n e (pcomp n (nat_lit 4) (nat_lit 15) ab c)))))

@[expose] noncomputable def c4K (n e a b c ab ac bc abc d : Nat) : Bool :=
  bAnd(commK n a d, bAnd(commK n b d, bAnd(commK n c d,
    bAnd(isoK n e (pcomp n (nat_lit 4) (nat_lit 15) a d),
    bAnd(isoK n e (pcomp n (nat_lit 4) (nat_lit 15) b d),
    bAnd(isoK n e (pcomp n (nat_lit 4) (nat_lit 15) c d),
    bAnd(isoK n e (pcomp n (nat_lit 4) (nat_lit 15) ab d),
    bAnd(isoK n e (pcomp n (nat_lit 4) (nat_lit 15) ac d),
    bAnd(isoK n e (pcomp n (nat_lit 4) (nat_lit 15) bc d),
      isoK n e (pcomp n (nat_lit 4) (nat_lit 15) abc d))))))))))

@[expose] noncomputable def rankK (n : Nat) (PT : Nat → Nat) (I : List Nat) : Bool :=
  strictB (pidn n (nat_lit 4)) fun e =>
    allL I fun ka => strictB (PT ka) fun a => allL I fun kb => strictB (PT kb) fun b =>
      strictB (pcomp n (nat_lit 4) (nat_lit 15) a b) fun ab =>
        bIf(c2K n e a b ab, allL I fun kc => strictB (PT kc) fun c =>
          bIf(c3K n e a b ab c,
            strictB (pcomp n (nat_lit 4) (nat_lit 15) a c) fun ac =>
              strictB (pcomp n (nat_lit 4) (nat_lit 15) b c) fun bc =>
                strictB (pcomp n (nat_lit 4) (nat_lit 15) ab c) fun abc =>
                  allL I fun kd => strictB (PT kd) fun d => notB (c4K n e a b c ab ac bc abc d),
            true), true)

@[expose] noncomputable def eightE (n : Nat) (E : List Nat) : Bool :=
  bAnd(allN (nat_lit 8) fun i => allN (nat_lit 8) fun j =>
      strictB (pcomp n (nat_lit 4) (nat_lit 15) (getL (nat_lit 0) E i) (getL (nat_lit 0) E j))
        fun z => memL z E,
    allN (nat_lit 8) fun i => allN i fun j =>
      notB (Nat.beq (getL (nat_lit 0) E i) (getL (nat_lit 0) E j)))

@[expose] noncomputable def eightSubK (n e a b c ab : Nat) : Bool :=
  strictB (pcomp n (nat_lit 4) (nat_lit 15) a c) fun ac =>
    strictB (pcomp n (nat_lit 4) (nat_lit 15) b c) fun bc =>
      strictB (pcomp n (nat_lit 4) (nat_lit 15) ab c) fun abc =>
        eightE n [e, a, b, ab, c, ac, bc, abc]

@[expose] noncomputable def eightK (n : Nat) (PT : Nat → Nat) (I : List Nat) : Bool :=
  strictB (pidn n (nat_lit 4)) fun e =>
    anyL I fun ka => strictB (PT ka) fun a => anyL I fun kb => strictB (PT kb) fun b =>
      strictB (pcomp n (nat_lit 4) (nat_lit 15) a b) fun ab =>
        bAnd(c2K n e a b ab, anyL I fun kc => strictB (PT kc) fun c =>
          bAnd(c3K n e a b ab c, eightSubK n e a b c ab))

@[expose] noncomputable def halfK (n N : Nat) (PT : Nat → Nat) (I : List Nat) : Bool :=
  strictB (pidn n (nat_lit 4)) fun e =>
    anyL I fun k => strictB (PT k) fun t =>
      bAnd(allN N fun j => strictB (PT j) fun x => commK n t x,
        anyN N fun s => strictB (PT s) fun x =>
          bAnd(dblK n e x, bAnd(commK n x t, isoK n e (pcomp n (nat_lit 4) (nat_lit 15) x t))))

end CFSG.KC.BalanceSC

end
