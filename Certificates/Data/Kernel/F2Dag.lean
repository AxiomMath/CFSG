module

public import Certificates.Data.Kernel.M1F2

public section

namespace CFSG.KC.F2Dag

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2

@[expose] noncomputable def powL (d X e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (idF d) (fun _ acc => mulF d acc X) e

@[expose] noncomputable def getB (d : Nat) (T : List Nat) (L i : Nat) : Nat :=
  nIf(Nat.blt i L, T.getD i (idF d), idF d)

@[expose] noncomputable def letterK (d : Nat) (E EI : List Nat) (L : Nat) (j : Int) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun k => Nat.rec (motive := fun _ => Nat) (getB d EI L (nat_lit 0)) (fun k' _ => getB d E L k') k)
    (fun k => getB d EI L k) j

@[expose] noncomputable def wordK (d : Nat) (E EI : List Nat) (L : Nat) (w : List Int) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun j _ ih acc => strictN (mulF d acc (letterK d E EI L j)) ih) w (idF d)

@[expose] noncomputable def canonF (d X : Nat) : Bool := Nat.blt X (pw2 (Nat.mul d d))

@[expose] noncomputable def stepsK (d nb : Nat) (E EI : List Nat) (ws : List (List Int)) :
    Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih s => andB (Nat.beq (E.getD (Nat.add nb s) (nat_lit 0))
      (wordK d E EI (Nat.add nb s) w)) (ih (Nat.succ s))) ws

@[expose] noncomputable def dagK (d nb : Nat) (ws : List (List Int)) (E EI : List Nat) : Bool :=
  andB (Nat.beq E.length (Nat.add nb ws.length)) (andB (Nat.beq EI.length (Nat.add nb ws.length))
    (andB (allN E.length fun k => andB (canonF d (E.getD k (nat_lit 0)))
      (andB (canonF d (EI.getD k (nat_lit 0)))
        (Nat.beq (mulF d (E.getD k (nat_lit 0)) (EI.getD k (nat_lit 0))) (idF d))))
      (stepsK d nb E EI ws (nat_lit 0))))

end CFSG.KC.F2Dag

end
