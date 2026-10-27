module

public import Certificates.Data.Kernel.Misc.Hyp

public section

namespace CFSG.KC.Misc.Hyp

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O73 CFSG.KC.Misc.T46
  CFSG.KC.Misc.Polar CFSG.KC.Misc.Lines CFSG.KC.Misc.Xi

@[expose] noncomputable def minAccK (PB LI : Nat → Nat) (NL : Nat → List Nat) (I X : Nat) : Nat :=
  letN (Nat.xor (Nat.lor I X) (Nat.sub (Nat.shiftLeft 1 693) 1)) fun U0 =>
  Nat.rec (motive := fun _ => Nat) (Nat.mul 1024 2048) (fun x acc => letN acc fun acc =>
    Bool.rec (motive := fun _ => Nat) acc
      (letN (pop1024 (candK LI NL x I X)) fun c => Bool.rec (motive := fun _ => Nat) acc
        (Nat.add (Nat.mul 1024 c) x) (Nat.blt c (Nat.div acc 1024)))
      (andB (bitK I x) (notB (Nat.beq (Nat.land (PB x) U0) 0))))
    693

@[expose] noncomputable def branchK (LB : Nat → Nat) (NL : Nat → List Nat) (go : Nat → Nat → Nat)
    (x C S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 1 (fun j acc => letN acc fun acc =>
    Bool.rec (motive := fun _ => Nat) acc
      (letN (extK LB NL x j S) fun S' =>
        combK acc (go (Nat.land S' (Nat.sub (Nat.shiftLeft 1 693) 1)) (Nat.shiftRight S' 693)))
      (bitK C j)) 1024

@[expose] noncomputable def runK (PB LB LI : Nat → Nat) (NL : Nat → List Nat) (fuel : Nat) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => 0) (fun _ ih I X => letN I fun I =>
    letN X fun X => Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat)
        (letN (passK PB LB LI NL I X) fun r => Bool.rec (motive := fun _ => Nat)
          (Bool.rec (motive := fun _ => Nat)
            (letN (minAccK PB LI NL I X) fun a => Bool.rec (motive := fun _ => Nat)
              (letN (Nat.mod a 1024) fun x =>
                branchK LB NL ih x (candK LI NL x I X) (Nat.lor I (Nat.shiftLeft X 693)))
              0 (Nat.beq a (Nat.mul 1024 2048)))
            (ih (Nat.land r (Nat.sub (Nat.shiftLeft 1 693) 1))
              (Nat.land (Nat.shiftRight r 693) (Nat.sub (Nat.shiftLeft 1 693) 1)))
            (bitK r 1387))
          1 (bitK r 1386))
        (Nat.add 2 I) (Nat.beq (Nat.lor I X) (Nat.sub (Nat.shiftLeft 1 693) 1)))
      1 (notB (Nat.beq (Nat.land I X) 0))) fuel

@[expose] noncomputable def searchK (PB LB HS LI : Nat → Nat) (NL : Nat → List Nat) (RES : Nat)
    (lo n : Nat) : Bool :=
  letB (PB 0) fun P0 => allN n fun d => letB (Nat.add lo d) fun j => impB (Nat.blt j 1024) <|
    letB (LB j) fun L => letB (runK PB LB LI NL 40 L (Nat.land P0 (Nat.xor L
      (Nat.sub (Nat.shiftLeft 1 693) 1)))) fun r => letB (at' 13 RES j) fun e =>
      Bool.rec (motive := fun _ => Bool)
        (andB (Nat.blt e 4225) (Nat.beq r (Nat.add 2 (HS (Nat.pred e))))) (Nat.beq r 1) (Nat.beq e 0)

end CFSG.KC.Misc.Hyp

end
