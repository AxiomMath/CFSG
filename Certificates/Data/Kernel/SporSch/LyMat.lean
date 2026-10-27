module

public import CFSG.Certificates.Kernel.Orders.Mat
public import Certificates.Data.Kernel.SporSch.F2Mat
public import Certificates.Data.Kernel.SporSch.Closure

public section

namespace CFSG.KS.SporSch.LyM

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.KC.Ord

@[expose] noncomputable def payRunP (p d w S : Nat) (cs : List Char) : Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ M => M)
    (fun ch _ ih ph idx M => strictN (Char.toNat ch) (fun c =>
      nIf(Nat.beq ph (nat_lit 0),
        nIf(Nat.beq c (nat_lit 10), ih (nat_lit 1) idx M, ih (nat_lit 0) idx M),
        nIf(wsK c, ih (nat_lit 1) idx M,
          strictN (nIf(Nat.blt idx (Nat.mul d d),
              Nat.lor M (Nat.shiftLeft
                (Nat.mod (nIf(bAnd(Nat.ble (nat_lit 48) c, Nat.ble c (nat_lit 57)),
                  Nat.sub c (nat_lit 48), nat_lit 0)) p)
                (Nat.add (Nat.mul S (Nat.div idx d)) (Nat.mul w (Nat.mod idx d)))), M)) (fun M' =>
            strictN (Nat.succ idx) (fun idx' => ih (nat_lit 1) idx' M'))))))
    cs

@[expose] noncomputable def letterR (G GI : Nat → Nat) (l : Int) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun k => nIf(Nat.beq k (nat_lit 0), GI (nat_lit 0), G (Nat.sub k (nat_lit 1))))
    (fun k => GI k) l

@[expose] noncomputable def wordR (p w S d T L H CM RM : Nat) (G GI : Nat → Nat) (X : Nat)
    (ws : List Int) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun X => X)
    (fun l _ ih X => strictN (mulR p w S d T L H CM RM X (letterR G GI l)) ih) ws X

@[expose] noncomputable def tokEq (v : Nat) (neg : Bool) (x : Int) : Bool :=
  Int.rec (motive := fun _ => Bool) (fun k => bIf(neg, false, Nat.beq k v))
    (fun k => bIf(neg, Nat.beq (Nat.succ k) v, false)) x

@[expose] noncomputable def parseRun (cs : List Char) : Nat → Bool → Nat → List Int → Bool → Bool :=
  List.rec (motive := fun _ => Nat → Bool → Nat → List Int → Bool → Bool)
    (fun _ _ _ L done => bAnd(done, List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L))
    (fun ch _ ih v neg len L done => strictB (Char.toNat ch) (fun c =>
      bIf(done, false,
      bIf(bAnd(Nat.ble (nat_lit 48) c, Nat.ble c (nat_lit 57)),
        strictB (Nat.add (Nat.mul v (nat_lit 10)) (Nat.sub c (nat_lit 48))) (fun v' =>
          strictB (Nat.succ len) (fun len' => ih v' neg len' L false)),
      bIf(Nat.beq c (nat_lit 45),
        bAnd(Nat.beq len (nat_lit 0), bIf(neg, false, ih (nat_lit 0) true (nat_lit 0) L false)),
      bIf(bIf(Nat.beq c (nat_lit 32), true, Nat.beq c (nat_lit 10)),
        bAnd(Nat.blt (nat_lit 0) len, bAnd(bIf(neg, Nat.blt (nat_lit 0) v, true),
          List.rec (motive := fun _ => Bool) false
            (fun x rest _ => bAnd(tokEq v neg x,
              ih (nat_lit 0) false (nat_lit 0) rest (Nat.beq c (nat_lit 10)))) L)),
        false))))))
    cs

@[expose] noncomputable def parseK (cs : List Char) (L : List Int) : Bool :=
  parseRun cs (nat_lit 0) false (nat_lit 0) L false

@[expose] noncomputable def stepB (p w S d T L H CM RM : Nat) (UG E W : Nat → Nat) (c h k cur : Nat) :
    Nat :=
  nIf(Nat.blt h cur,
    strictN (mulR p w S d T L H CM RM (UG k) (E h)) (fun y =>
    strictN fld(W h, Nat.mul (nat_lit 9) k, nat_lit 511) (fun j =>
      nIf(bAnd(Nat.blt j cur, Nat.beq y (E j)), cur,
        nIf(bAnd(Nat.beq j cur, bAnd(Nat.blt cur c, Nat.beq y (E cur))), Nat.succ cur,
          CFSG.KS.SporSch.failC)))),
    cur)

@[expose] noncomputable def runB (p w S d T L H CM RM : Nat) (UG E W : Nat → Nat) (kg c : Nat) :
    Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ cur => cur)
    (fun _ ih h cur => strictN (foldUp kg (fun k cur =>
        stepB p w S d T L H CM RM UG E W c h k cur) cur) (fun c' =>
      strictN (Nat.succ h) (fun h' => ih h' c')))

@[expose] noncomputable def sortB (E SO SOI : Nat → Nat) (c i : Nat) : Bool :=
  strictB (SO i) (fun j => bAnd(Nat.blt j c, bAnd(Nat.beq (SOI j) i,
    bIf(Nat.blt (Nat.succ i) c, Nat.blt (E j) (E (SO (Nat.succ i))), true))))

@[expose] noncomputable def powR (p w S d T L H CM RM ONE M e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ONE
    (fun _ acc => strictN acc (fun a => mulR p w S d T L H CM RM a M)) e

end CFSG.KS.SporSch.LyM

end
