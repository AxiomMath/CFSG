module

public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.Spor.Text

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Text

@[expose] noncomputable def hexTabRun (wd n w cnt : Nat) (F : Nat → Nat) (cs : List Char) :
    Nat → Nat → Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool)
    (fun j e t _ _ => bAnd(Nat.beq j cnt, bAnd(Nat.beq e (nat_lit 0), Nat.beq t (nat_lit 0))))
    (fun ch _ ih j e t v acc => strictB (hexV (Char.toNat ch)) (fun h =>
      bIf(Nat.blt h (nat_lit 16), bIf(Nat.blt j cnt,
        strictB (Nat.add (Nat.mul v (nat_lit 16)) h) (fun v' =>
        bIf(Nat.beq (Nat.succ t) wd,
          bIf(Nat.blt v' (Nat.shiftLeft (nat_lit 1) w),
            strictB (Nat.lor acc (Nat.shiftLeft v' (Nat.mul w e))) (fun acc' =>
            strictB (Nat.succ e) (fun e' =>
              bIf(Nat.beq e' n,
                bAnd(Nat.beq acc' (F j),
                  strictB (Nat.succ j) (fun j' => ih j' (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0))),
                ih j e' (nat_lit 0) (nat_lit 0) acc'))),
            false),
          strictB (Nat.succ t) (fun t' => ih j e t' v' acc))),
        false), false)))
    cs

@[expose] noncomputable def hexTabK (cs : List Char) (wd n w cnt : Nat) (F : Nat → Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) wd, bAnd(Nat.blt (nat_lit 0) n,
    hexTabRun wd n w cnt F cs (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0)))

@[expose] noncomputable def evRK (w : Nat) (Ws : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun t _ ih p => strictN (pg w (mask w) t p) ih) Ws p

@[expose] noncomputable def evPowK (w : Nat) (Ws : List Nat) (e p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) p (fun _ q => strictN q (evRK w Ws)) e

@[expose] noncomputable def fixBK (w : Nat) (bs : List Nat) (Ws : List Nat) (e : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => bAnd(Nat.beq (evPowK w Ws e b) b, ih)) bs

@[expose] noncomputable def canonL (n w : Nat) (Ws : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun t _ ih => bAnd(canonK n w (mask w) (Nat.mul n w) t, ih)) Ws

@[expose] noncomputable def ltL (n : Nat) (bs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun b _ ih => bAnd(Nat.blt b n, ih)) bs

@[expose] noncomputable def ordB0 (w : Nat) (bs : List Nat) (Ws : List Nat) (m : Nat) : Bool :=
  bAnd(fixBK w bs Ws m, allN (Nat.succ m) (fun d =>
    bIf(bAnd(Nat.blt (nat_lit 1) d, Nat.beq (Nat.mod m d) (nat_lit 0)),
      bIf(fixBK w bs Ws (Nat.div m d), false, true), true)))

@[expose] noncomputable def ordWK (n w : Nat) (bs : List Nat) (Ws : List Nat) (m : Nat) : Bool :=
  bAnd(canonL n w Ws, bAnd(ltL n bs, ordB0 w bs Ws m))

end CFSG.KS.SporSch

end
