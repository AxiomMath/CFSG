module

public import Certificates.Data.Kernel.M1F2
public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KC.SurjK

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2
open CFSG.KS (lget)

@[expose] noncomputable def parB (d X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => nIf(bit X i, Nat.xor acc (nat_lit 1), acc)) d

@[expose] noncomputable def mvK (d M v : Nat) : Nat :=
  orN d fun i => Nat.shiftLeft (parB d (Nat.land (rowF d M i) v)) i

@[expose] noncomputable def matW (d : Nat) (F : Int → Nat) (w : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) (idF d) (fun z _ ih => strictN ih fun T => mulF d (F z) T) w

@[expose] noncomputable def baseF (A AI B BI : Nat) (z : Int) : Nat :=
  nIf(Nat.beq z.toNat 0, A, nIf(Nat.beq z.toNat 1, AI, nIf(Nat.beq z.toNat 2, B, BI)))

@[expose] noncomputable def imgF (Ims ImsI : List Nat) (z : Int) : Nat :=
  nIf(Nat.blt 0 z.natAbs, nIf(decide (0 < z), lget Ims (z.natAbs - 1), lget ImsI (z.natAbs - 1)),
    nat_lit 0)

@[expose] noncomputable def digV (c : Nat) : Nat :=
  nIf(andB (Nat.ble (nat_lit 48) c) (Nat.ble c (nat_lit 57)), Nat.sub c (nat_lit 48), nat_lit 10)

@[expose] noncomputable def tokV (sg v : Nat) : Int := bif Nat.beq sg 1 then -(v : Int) else (v : Int)

@[expose] noncomputable def nilB {α : Type} (L : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L

@[expose] noncomputable def wordsRun (cs : List Char) :
    List (List Int) → List Int → Nat → Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => List (List Int) → List Int → Nat → Nat → Nat → Nat → Bool)
    (fun L W st sg v _ => bIf(Nat.beq st 2,
      List.rec (motive := fun _ => Bool) false (fun x xs _ =>
        bAnd(decide (x = tokV sg v), bAnd(nilB xs, nilB L))) W,
      bAnd(Nat.beq st 0, bAnd(nilB W, nilB L))))
    (fun ch _ ih L W st sg v ln => strictB (Char.toNat ch) fun c =>
      bIf(Nat.blt (digV c) 10,
        bIf(Nat.beq st 0,
          bIf(Nat.beq ln 0,
            List.rec (motive := fun _ => Bool) false (fun W' L' _ => ih L' W' 2 0 (digV c) 1) L,
            ih L W 2 0 (digV c) 1),
          ih L W 2 sg (Nat.add (Nat.mul v 10) (digV c)) 1),
      bIf(Nat.beq c 45, bAnd(Nat.beq st 0,
          bIf(Nat.beq ln 0,
            List.rec (motive := fun _ => Bool) false (fun W' L' _ => ih L' W' 1 1 0 1) L,
            ih L W 1 1 0 1)),
      bIf(Nat.beq c 32, bAnd(Nat.beq st 2,
          List.rec (motive := fun _ => Bool) false
            (fun x xs _ => bAnd(decide (x = tokV sg v), ih L xs 0 0 0 1)) W),
      bIf(Nat.beq c 10,
        bIf(Nat.beq st 2,
          List.rec (motive := fun _ => Bool) false (fun x xs _ =>
            bAnd(decide (x = tokV sg v), bAnd(nilB xs, ih L [] 0 0 0 0))) W,
          bAnd(Nat.beq st 0, bAnd(Nat.beq ln 0, ih L W 0 0 0 0))),
        false)))))
    cs

@[expose] noncomputable def wordsK (cs : List Char) (L : List (List Int)) : Bool :=
  bAnd(L.all (fun w => !nilB w), wordsRun cs L [] 0 0 0 0)

@[expose] noncomputable def orbStep (d n A B v0 : Nat) (PT PA LB AP BP SO SOI : Nat → Nat)
    (k : Nat) : Bool :=
  strictB (PT k) fun p =>
  bAnd(Nat.blt p (Nat.shiftLeft 1 d),
  bAnd(bIf(Nat.beq k 0, Nat.beq p v0,
    bAnd(Nat.blt (PA k) k, bAnd(Nat.blt (LB k) 2,
      Nat.beq p (mvK d (nIf(Nat.beq (LB k) 0, A, B)) (PT (PA k)))))),
  bAnd(Nat.blt (AP k) n, bAnd(Nat.beq (PT (AP k)) (mvK d A p),
  bAnd(Nat.blt (BP k) n, bAnd(Nat.beq (PT (BP k)) (mvK d B p),
  bAnd(Nat.blt (SO k) n, bAnd(Nat.blt (SOI k) n, bAnd(Nat.beq (SO (SOI k)) k,
    bIf(Nat.blt (Nat.succ k) n, Nat.blt (PT (SO k)) (PT (SO (Nat.succ k))), true))))))))))

end CFSG.KC.SurjK

end
