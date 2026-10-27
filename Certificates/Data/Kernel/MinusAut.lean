module

public import Certificates.Data.Kernel.MinusQuandle

public section

namespace CFSG.KD.MinusAut

open CFSG.KD.MinusQuandle

@[expose] def isGen (t : ℕ) : Bool :=
  Nat.beq t 0 || Nat.beq t 1 || Nat.beq t 5 || Nat.beq t 15

@[expose] def gv (c1 c2 c3 t : ℕ) : ℕ :=
  if Nat.beq t 0 then 0 else if Nat.beq t 1 then c1 else if Nat.beq t 5 then c2 else c3

@[expose] def val (R : ℕ → ℕ) (P X Y c1 c2 c3 t d : ℕ) : ℕ :=
  if isGen t then gv c1 c2 c3 t
  else tq R (lane 7 d (lane 7 P (lane 7 X t))) (lane 7 d (lane 7 P (lane 7 Y t)))

@[expose] def extFrom (R : ℕ → ℕ) (P X Y c1 c2 c3 d₀ lo m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) d₀ (fun k acc => force acc fun acc =>
    Nat.lor acc (Nat.shiftLeft (val R P X Y c1 c2 c3 (Nat.add lo k) acc)
      (Nat.mul 7 (lane 7 P (Nat.add lo k))))) m

@[expose] def ext (R : ℕ → ℕ) (P X Y c1 c2 c3 n : ℕ) : ℕ :=
  extFrom R P X Y c1 c2 c3 0 0 n

@[expose] def recOK (R : ℕ → ℕ) (P X Y c1 c2 c3 n d : ℕ) : Bool :=
  allF n fun t => Nat.blt (lane 7 d (lane 7 P t)) 65 &&
    Nat.beq (lane 7 d (lane 7 P t)) (val R P X Y c1 c2 c3 t d)

@[expose] def homOn (R : ℕ → ℕ) (P Q n d : ℕ) : Bool :=
  allF n fun a => allF n fun b =>
    !(Nat.blt (lane 7 Q (tq R (lane 7 P a) (lane 7 P b))) n) ||
      Nat.beq (lane 7 d (tq R (lane 7 P a) (lane 7 P b)))
        (tq R (lane 7 d (lane 7 P a)) (lane 7 d (lane 7 P b)))

@[expose] def failsD (R : ℕ → ℕ) (P X Y Q c1 c2 c3 n d : ℕ) : Bool :=
  recOK R P X Y c1 c2 c3 n d && !(homOn R P Q n d)

@[expose] def key (c1 c2 c3 : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul 4225 c1) (Nat.mul 65 c2)) c3

@[expose] def wact (R : ℕ → ℕ) (w : List ℕ) (q : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) q (fun i _ acc => tq R i acc) w

@[expose] def wordOK (w : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun i _ acc => Nat.blt i 65 && acc) w

@[expose] def kmask (H : List (ℕ × ℕ × ℕ × List ℕ)) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun e _ acc => Nat.lor (Nat.shiftLeft 1 (key e.1 e.2.1 e.2.2.1)) acc) H

@[expose] def entryOK (R : ℕ → ℕ) (P X Y : ℕ) (e : ℕ × ℕ × ℕ × List ℕ) : Bool :=
  Nat.blt e.1 65 && Nat.blt e.2.1 65 && Nat.blt e.2.2.1 65 && wordOK e.2.2.2 &&
    force (ext R P X Y e.1 e.2.1 e.2.2.1 65) fun d =>
      recOK R P X Y e.1 e.2.1 e.2.2.1 65 d &&
        allF 65 fun q => Nat.beq (wact R e.2.2.2 q) (lane 7 d q)

@[expose] def homsOK (R : ℕ → ℕ) (P X Y : ℕ) (H : List (ℕ × ℕ × ℕ × List ℕ)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ acc => entryOK R P X Y e && acc) H

@[expose] def ordOK (R : ℕ → ℕ) (P X Y Q : ℕ) : Bool :=
  Nat.beq (lane 7 P 0) 0 && Nat.beq (lane 7 P 1) 19 && Nat.beq (lane 7 P 5) 1 &&
    Nat.beq (lane 7 P 15) 3 &&
  allF 65 (fun t => Nat.blt (lane 7 P t) 65 && Nat.beq (lane 7 Q (lane 7 P t)) t &&
    (isGen t || (Nat.blt (lane 7 X t) t && Nat.blt (lane 7 Y t) t &&
      Nat.beq (tq R (lane 7 P (lane 7 X t)) (lane 7 P (lane 7 Y t))) (lane 7 P t)))) &&
  allF 65 (fun q => Nat.blt (lane 7 Q q) 65 && Nat.beq (lane 7 P (lane 7 Q q)) q)

@[expose] def mainA (R : ℕ → ℕ) (P X Y Q K c1 : ℕ) : Bool :=
  Nat.beq c1 0 || force (ext R P X Y c1 0 0 5) (failsD R P X Y Q c1 0 0 5) || allF 65 fun c2 =>
    Nat.beq c2 0 || Nat.beq c2 c1 || force (ext R P X Y c1 c2 0 15) fun d15 =>
      failsD R P X Y Q c1 c2 0 15 d15 || allF 65 fun c3 =>
        Nat.beq c3 0 || Nat.beq c3 c1 || Nat.beq c3 c2 || Nat.testBit K (key c1 c2 c3) ||
          force (extFrom R P X Y c1 c2 c3 d15 15 3) (failsD R P X Y Q c1 c2 c3 18)

@[expose] def mainOK (R : ℕ → ℕ) (P X Y Q K lo m : ℕ) : Bool :=
  allF m fun k => mainA R P X Y Q K (Nat.add lo k)

@[expose] def transAux (R : ℕ → ℕ) (W : List (List ℕ)) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun w _ acc i => wordOK w && Nat.beq (wact R w 0) i && acc (Nat.succ i)) W

@[expose] def transOK (R : ℕ → ℕ) (W : List (List ℕ)) : Bool :=
  Nat.beq W.length 65 && transAux R W 0

end CFSG.KD.MinusAut
