module

public import Certificates.Data.Kernel.LyS0.Check

public section

namespace CFSG.KC.Fi22Cls

open CFSG.KD.LyS0

@[expose] noncomputable def wordsT (wo wd : Nat → Nat) (nl : Nat) : List Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool)
    (fun c i => bAnd(Nat.beq c nl, Nat.beq i (wo nl)))
    (fun x _ ih c i => bIf(Nat.blt i (wo c),
      bAnd(Nat.beq x (wd i), ih c (Nat.succ i)),
      bAnd(Nat.blt c nl, bAnd(Nat.beq i (wo c),
        bAnd(Nat.beq x (Nat.sub (wo (Nat.succ c)) (wo c)), ih (Nat.succ c) i)))))

@[expose] noncomputable def wordsOK (wo wd : Nat → Nat) (nl : Nat) (cs : List Char) : Bool :=
  textOK cs && wordsT wo wd nl (natsL cs) 0 (wo 0)

end CFSG.KC.Fi22Cls

end
