module

public import Certificates.Data.Kernel.SporSch.PairJ3Cert
public import Certificates.Data.Kernel.SporSch.PairK

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS

structure ChainP where
  gens : List Nat
  base : List Nat
  strong : List Nat
  words : List (List Int)

structure RecP where
  rep : Nat
  conj : List (List Int)
  chain : ChainP

structure SylP where
  prime : Nat
  gens : List Nat
  records : List RecP

@[expose] noncomputable def fldI (w P k : Nat) : Nat → List Int → List Int :=
  Nat.rec (motive := fun _ => Nat → List Int → List Int) (fun _ tl => tl)
    (fun _ ih s tl => Int.ofNat (pg w (mask w) P s) :: ih (Nat.succ s) tl) k

@[expose] noncomputable def permsI (n w : Nat) (Ps : List Nat) (tl : List Int) : List Int :=
  List.rec (motive := fun _ => List Int) tl (fun P _ ih => fldI w P n (nat_lit 0) ih) Ps

@[expose] noncomputable def intsI (l : List Int) (tl : List Int) : List Int :=
  List.rec (motive := fun _ => List Int) tl (fun x _ ih => x :: ih) l

@[expose] noncomputable def wordsI (ws : List (List Int)) (tl : List Int) : List Int :=
  List.rec (motive := fun _ => List Int) tl (fun x _ ih => Int.ofNat (lenK x) :: intsI x ih) ws

@[expose] noncomputable def chainI (n w : Nat) (c : ChainP) (tl : List Int) : List Int :=
  ChainP.rec (motive := fun _ => List Int) (fun g b s wd =>
    Int.ofNat (lenK g) :: Int.ofNat (lenK b) :: Int.ofNat (lenK s) :: Int.ofNat (lenK wd) ::
      permsI n w g (natsI b (permsI n w s (wordsI wd tl)))) c

@[expose] noncomputable def recI (n w : Nat) (r : RecP) (tl : List Int) : List Int :=
  RecP.rec (motive := fun _ => List Int) (fun rp cj ch =>
    fldI w rp n (nat_lit 0) (Int.ofNat (lenK cj) :: wordsI cj (chainI n w ch tl))) r

@[expose] noncomputable def recsI (n w : Nat) (rs : List RecP) (tl : List Int) : List Int :=
  List.rec (motive := fun _ => List Int) tl (fun r _ ih => recI n w r ih) rs

@[expose] noncomputable def sylI (n w : Nat) (s : SylP) (tl : List Int) : List Int :=
  SylP.rec (motive := fun _ => List Int) (fun p g rs =>
    Int.ofNat p :: Int.ofNat (lenK g) :: permsI n w g (Int.ofNat (lenK rs) :: recsI n w rs tl)) s

@[expose] noncomputable def sylsI (n w : Nat) (ss : List SylP) (tl : List Int) : List Int :=
  List.rec (motive := fun _ => List Int) tl (fun s _ ih => sylI n w s ih) ss

@[expose] noncomputable def encSyl (n w : Nat) (ss : List SylP) : List Int :=
  Int.ofNat (lenK ss) :: sylsI n w ss []

@[expose] noncomputable def permK (n w P : Nat) : Bool :=
  permOK n w (mask w) (Nat.mul n w) P (pinvS n w (mask w) P)

@[expose] noncomputable def permsK (n w : Nat) (Ps : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun P _ ih => bAnd(permK n w P, ih)) Ps

@[expose] noncomputable def letterK (x : Int) : Bool :=
  Int.rec (motive := fun _ => Bool) (fun k => bIf(Nat.beq k (nat_lit 1), true, Nat.beq k (nat_lit 2)))
    (fun k => bIf(Nat.beq k (nat_lit 0), true, Nat.beq k (nat_lit 1))) x

@[expose] noncomputable def lettersK (ws : List (List Int)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x _ ih => bAnd(List.rec (motive := fun _ => Bool) true (fun a _ ih2 => bAnd(letterK a, ih2)) x,
      ih)) ws

@[expose] noncomputable def notMemK (x : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun y _ ih => bAnd(bIf(Nat.beq x y, false, true), ih)) l

@[expose] noncomputable def nodupK (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x xs ih => bAnd(notMemK x xs, ih)) l

@[expose] noncomputable def prefK (g : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun a _ ih s => List.rec (motive := fun _ => Bool) false (fun b s' _ => bAnd(Nat.beq a b, ih s')) s)
    g

@[expose] noncomputable def chainK (n w : Nat) (c : ChainP) : Bool :=
  ChainP.rec (motive := fun _ => Bool) (fun g b s wd =>
    bAnd(Nat.ble (lenK g) (lenK s), bAnd(ltL n b, bAnd(nodupK b, bAnd(permsK n w s,
      bAnd(prefK g s, Nat.beq (Nat.add (lenK wd) (lenK g)) (lenK s))))))) c

@[expose] noncomputable def recK (n w : Nat) (r : RecP) : Bool :=
  RecP.rec (motive := fun _ => Bool) (fun rp cj ch => bAnd(permK n w rp, bAnd(lettersK cj, chainK n w ch)))
    r

@[expose] noncomputable def sylsK (n w : Nat) (ss : List SylP) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun s _ ih => bAnd(SylP.rec (motive := fun _ => Bool)
    (fun _ g rs => bAnd(permsK n w g,
      List.rec (motive := fun _ => Bool) true (fun r _ ih2 => bAnd(recK n w r, ih2)) rs)) s, ih)) ss

end CFSG.KS.SporSch

end
