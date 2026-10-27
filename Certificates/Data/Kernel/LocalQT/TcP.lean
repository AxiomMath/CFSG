module

public import Certificates.Data.Kernel.LocalQT.Tc

public section

namespace CFSG.KC.LQT.TC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim

@[expose] noncomputable def letGP (idn : Nat) (G GI : List Nat) (z : Int)
    (k : Nat → Nat → Bool) : Bool :=
  Int.rec (motive := fun _ => Bool)
    (fun m => Nat.rec (motive := fun _ => Bool) (k idn idn)
      (fun j _ => k (getTc idn G j) (getTc idn GI j)) m)
    (fun m => k (getTc idn GI m) (getTc idn G m)) z

@[expose] noncomputable def wordP (n w idn : Nat) (G GI : List Nat) (wd : List Int)
    (k : Nat → Nat → Bool) : Bool :=
  List.rec (motive := fun _ => (Nat → Nat → Bool) → Bool) (fun k => k idn idn)
    (fun z _ ih k => ih fun A AI => letGP idn G GI z fun L LI =>
      strictB (pcomp n w (mask w) L A) fun B => strictB (pcomp n w (mask w) AI LI) fun BI =>
        k B BI) wd k

@[expose] noncomputable def letRP (idn : Nat) (r1 r2 : List Nat) (len : Nat) (z : Int)
    (k : Nat → Nat → Bool) : Bool :=
  Int.rec (motive := fun _ => Bool)
    (fun m => Nat.rec (motive := fun _ => Bool) (k idn idn)
      (fun j _ => k (regTc idn r1 len j) (regTc idn r2 len j)) m)
    (fun m => k (regTc idn r2 len m) (regTc idn r1 len m)) z

@[expose] noncomputable def runP (n w idn : Nat) (prog : List (Int × Int))
    (k : List Nat → List Nat → Nat → Bool) : List Nat → List Nat → Nat → Bool :=
  List.rec (motive := fun _ => List Nat → List Nat → Nat → Bool) k
    (fun pq _ ih r1 r2 len => letRP idn r1 r2 len pq.1 fun A AI => letRP idn r1 r2 len pq.2
      fun B BI => strictB (pcomp n w (mask w) A B) fun C => strictB (pcomp n w (mask w) BI AI)
        fun CI => ih (List.cons C r1) (List.cons CI r2) (Nat.succ len)) prog

@[expose] noncomputable def conjOneP (n w g gi : Nat) (T TI : List Nat)
    (k : List Nat → List Nat → Nat → Bool) : List Nat → List Nat → Nat → Bool :=
  List.rec (motive := fun _ => List Nat → List Nat → List Nat → Nat → Bool)
    (fun _ r1 r2 len => k r1 r2 len)
    (fun t _ ih TI' r1 r2 len => List.rec (motive := fun _ => Bool) false
      (fun ti TI'' _ => strictB (pcomp n w (mask w) (pcomp n w (mask w) g t) gi) fun C =>
        strictB (pcomp n w (mask w) g (pcomp n w (mask w) ti gi)) fun CI =>
          ih TI'' (List.cons C r1) (List.cons CI r2) (Nat.succ len)) TI') T TI

@[expose] noncomputable def conjsP (n w idn : Nat) (G GI TS TIS : List Nat) (ws : List (List Int))
    (k : List Nat → List Nat → Nat → Bool) : List Nat → List Nat → Nat → Bool :=
  List.rec (motive := fun _ => List Nat → List Nat → Nat → Bool) k
    (fun wd _ ih r1 r2 len => wordP n w idn G GI wd fun g gi =>
      conjOneP n w g gi TS TIS ih r1 r2 len) ws

@[expose] noncomputable def pairsOK (n w : Nat) (L LI : List Nat) : Bool := gensTc n w L LI

@[expose] noncomputable def mcP (n w : Nat) (G GI TS TIS : List Nat) (ws : List (List Int))
    (prog : List (Int × Int)) (targets : List Nat) : Bool :=
  bAnd(idK n w (mask w), bAnd(gensTc n w G GI, bAnd(pairsOK n w TS TIS,
    conjsP n w (pidn n w) G GI TS TIS ws
      (runP n w (pidn n w) prog (fun r1 _ _ => targTc n w targets r1)) List.nil List.nil
      (nat_lit 0))))

@[expose] noncomputable def selTc (idn : Nat) (r1 : List Nat) (len : Nat) (idx S : List Nat) :
    Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun S => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) S)
    (fun k _ ih S => List.rec (motive := fun _ => Bool) false
      (fun s S' _ => bAnd(Nat.blt k len, bAnd(Nat.beq (regTc idn r1 len k) s, ih S'))) S) idx S

@[expose] noncomputable def pushP (G GI : List Nat) (k : List Nat → List Nat → Nat → Bool) :
    List Nat → List Nat → Nat → Bool :=
  List.rec (motive := fun _ => List Nat → List Nat → List Nat → Nat → Bool)
    (fun _ r1 r2 len => k r1 r2 len)
    (fun g _ ih GI' r1 r2 len => List.rec (motive := fun _ => Bool) false
      (fun gi GI'' _ => ih GI'' (List.cons g r1) (List.cons gi r2) (Nat.succ len)) GI') G GI

@[expose] noncomputable def runSelP (n w : Nat) (G GI : List Nat) (prog : List (Int × Int))
    (idx S : List Nat) : Bool :=
  bAnd(idK n w (mask w), bAnd(gensTc n w G GI,
    pushP G GI (runP n w (pidn n w) prog (fun r1 _ len => selTc (pidn n w) r1 len idx S))
      List.nil List.nil (nat_lit 0)))

end CFSG.KC.LQT.TC

end
