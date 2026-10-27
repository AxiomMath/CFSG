module

public import Certificates.Data.Kernel.SurjK

public section

namespace CFSG.KC.WordsT

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.SurjK

@[expose] noncomputable def wordsRunT (cs : List Char) :
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
          bAnd(Nat.beq st 0, bAnd(nilB W, ih L [] 0 0 0 0))),
        false)))))
    cs

@[expose] noncomputable def wordsT (cs : List Char) (L : List (List Int)) : Bool :=
  bAnd(L.all (fun w => !nilB w), wordsRunT cs L [] 0 0 0 0)

end CFSG.KC.WordsT

end
