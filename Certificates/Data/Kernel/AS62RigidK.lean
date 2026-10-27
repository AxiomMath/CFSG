module

public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KC.AS62

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 45 6 (mask 6) p q

@[expose] noncomputable def PID : Nat := pidn 45 6

@[expose] noncomputable def bitK (R j : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight R j) 1) 1

@[expose] noncomputable def tup5 (a b c d e : Nat) (l : Nat) : Nat :=
  nIf(Nat.beq l 0, a, nIf(Nat.beq l 1, b, nIf(Nat.beq l 2, c, nIf(Nat.beq l 3, d, e))))

@[expose] noncomputable def codeW {k : Nat} (E EI : Nat → Nat) (code : Fin k → Nat)
    (w : List (Fin k × Bool)) : Nat :=
  w.foldr (fun l acc => pc (Bool.rec (motive := fun _ => Nat) (EI (code l.1)) (E (code l.1)) l.2)
    acc) PID

@[expose] noncomputable def evalK {k : Nat} (E EI : Nat → Nat) (w : List (Fin k × Bool)) : Nat :=
  codeW E EI (fun i => i.val) w

@[expose] noncomputable def relK {k : Nat} (E EI : Nat → Nat) (w : List (Fin k × Bool)) : Bool :=
  Nat.beq (evalK E EI w) PID

@[expose] noncomputable def beqB (x y : Bool) : Bool := bIf(x, y, bIf(y, false, true))

@[expose] noncomputable def notMemK (x : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun y _ ih => bIf(Nat.beq y x, false, ih)) L

@[expose] noncomputable def nodupK (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x xs ih => bAnd(notMemK x xs, ih)) L

end CFSG.KC.AS62

end
