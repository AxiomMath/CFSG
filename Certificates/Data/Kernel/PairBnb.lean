module

public section

namespace CFSG.KC.PairBnb

@[expose] noncomputable def forceN {β : Sort _} (y : Nat) (k : Nat → β) : β :=
  Nat.rec (motive := fun _ => β) (k 0) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def logT : Nat :=
  887133499996772749431388771845841818521994975247091718529068305853617984204216612754432979924158408807141277358640337790034654564915437049669086536098580320958494672827870480950005428442068881363029033210543031286029590315679758012285751609291502718800280474369624060000835416630539061412756340368107892935894982605545851628839301541124992486237770331566235387252043958957488041855504789160467065383242479533570529851566123953511881052146263155718953081811739358748252172429836387777355970565809517814466395664784778439423225044997507833381850957502249489212999473577676371921324003856900945123923710851587141337088

@[expose] noncomputable def hb8 (y o : Nat) : Nat :=
  Nat.add o (Nat.land (Nat.shiftRight logT (Nat.shiftLeft y 3)) 255)

@[expose] noncomputable def hb16 (y o : Nat) : Nat :=
  forceN (Nat.shiftRight y 8) fun a => Bool.rec (hb8 a (Nat.add o 8)) (hb8 y o) (Nat.beq a 0)

@[expose] noncomputable def hb32 (y o : Nat) : Nat :=
  forceN (Nat.shiftRight y 16) fun a => Bool.rec (hb16 a (Nat.add o 16)) (hb16 y o) (Nat.beq a 0)

@[expose] noncomputable def hb64 (y o : Nat) : Nat :=
  forceN (Nat.shiftRight y 32) fun a => Bool.rec (hb32 a (Nat.add o 32)) (hb32 y o) (Nat.beq a 0)

@[expose] noncomputable def hb128 (y o : Nat) : Nat :=
  forceN (Nat.shiftRight y 64) fun a => Bool.rec (hb64 a (Nat.add o 64)) (hb64 y o) (Nat.beq a 0)

@[expose] noncomputable def hbR (x : Nat) : Nat :=
  Bool.rec (Nat.log2 x) (hb128 x 0) (Nat.blt x 340282366920938463463374607431768211456)

@[expose] noncomputable def growR (nbf wtf : Nat → Nat) (fuel : Nat) : Nat → Nat → Nat → Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat × Nat) (fun _ C mx => (C, mx))
    (fun _ ih cand C mx => Bool.rec
      (forceN (hbR cand) fun l => forceN (Nat.land cand (nbf l)) fun c' =>
        forceN (Nat.lor C (Nat.pow 2 l)) fun C' => forceN (wtf l) fun w =>
          forceN (Bool.rec mx w (Nat.ble mx w)) fun m' => ih c' C' m')
      (C, mx) (Nat.beq cand 0)) fuel

@[expose] noncomputable def boundR (nbf wtf : Nat → Nat) (fuel : Nat) : Nat → Option Nat :=
  Nat.rec (motive := fun _ => Nat → Option Nat)
    (fun mask => Bool.rec none (some 0) (Nat.beq mask 0))
    (fun _ ih mask => Bool.rec
      (forceN (hbR mask) fun l =>
        Prod.rec (motive := fun _ => Option Nat)
          (fun C mx => forceN (Nat.xor mask C) fun m' =>
            Option.rec (motive := fun _ => Option Nat) none (fun b => some (Nat.add b mx)) (ih m'))
          (growR nbf wtf 256 (Nat.land mask (nbf l)) (Nat.pow 2 l) (wtf l)))
      (some 0) (Nat.beq mask 0)) fuel

@[expose] noncomputable def findR (mask : Nat) (order : List Nat) : Option Nat :=
  List.rec (motive := fun _ => Option Nat) none
    (fun v _ ih => Bool.rec ih (some v) (Nat.blt 0 (Nat.land mask (Nat.shiftLeft 1 v)))) order

@[expose] noncomputable def bnbR (nbf wtf : Nat → Nat) (order : List Nat) (fuel : Nat) :
    Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => false)
    (fun _ ih mask budget =>
      Bool.rec
        (Option.rec (motive := fun _ => Bool) false
          (fun v => forceN (wtf v) fun w =>
            Bool.rec false
              (Bool.rec false
                (forceN (Nat.xor mask (Nat.pow 2 v)) fun m2 => ih m2 budget)
                (forceN (Nat.xor mask (Nat.land mask (Nat.lor (nbf v) (Nat.pow 2 v)))) fun m1 =>
                  ih m1 (Nat.sub budget w)))
              (Nat.ble w budget))
          (findR mask order))
        true
        (Option.rec (motive := fun _ => Bool) false (fun b => Nat.ble b budget)
          (boundR nbf wtf 256 mask))) fuel

@[expose] noncomputable def wtF (nW wR wW : Nat) (v : Nat) : Nat := Bool.rec wR wW (Nat.blt v nW)

@[expose] noncomputable def packT : List Nat → Nat :=
  List.rec 0 fun x _ ih => Nat.lor x (Nat.shiftLeft ih 128)

@[expose] noncomputable def nbP (T v : Nat) : Nat :=
  Nat.land (Nat.shiftRight T (Nat.shiftLeft v 7)) 340282366920938463463374607431768211455

@[expose] noncomputable def spR (order : List Nat) (m k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) m (fun _ s => forceN s fun s' =>
    Option.rec (motive := fun _ => Nat) s' (fun v => Nat.xor s' (Nat.pow 2 v)) (findR s' order)) k

@[expose] noncomputable def leafR (nbf wtf : Nat → Nat) (order : List Nat) (fuel budget m k : Nat) :
    Bool :=
  forceN (spR order m k) fun s =>
    Option.rec (motive := fun _ => Bool) false
      (fun v => forceN (wtf v) fun w =>
        Bool.rec false
          (bnbR nbf wtf order (Nat.sub (Nat.sub fuel k) 1)
            (Nat.xor s (Nat.land s (Nat.lor (nbf v) (Nat.pow 2 v)))) (Nat.sub budget w))
          (Nat.ble w budget))
      (findR s order)

end CFSG.KC.PairBnb
