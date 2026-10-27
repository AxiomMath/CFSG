module

public import Certificates.Data.Kernel.SporCov.LaneKit

public section

namespace CFSG.KC.SporCov

@[expose] noncomputable def snocR (Rg : List Nat) (x : Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) (List.cons x List.nil) (fun a _ ih => List.cons a ih) Rg

@[expose] noncomputable def regC (mul : Nat → Nat → Nat) (ONE MA MAi MB MBi : Nat)
    (Ws : List (List Nat)) : List Nat → (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => List Nat → (List Nat → Bool) → Bool) (fun Rg k => k Rg)
    (fun w _ ih Rg k => forceR (mwLn mul (letLn MA MAi MB MBi ONE Rg) w ONE) fun x =>
      ih (snocR Rg x) k) Ws

@[expose] noncomputable def kitC (mul : Nat → Nat → Nat) (ONE MA MAi MB MBi : Nat)
    (Ws : List (List Nat)) (k : (List Nat → Nat) → Bool) : Bool :=
  forceR MA fun A => forceR MAi fun Ai => forceR MB fun B => forceR MBi fun Bi =>
    Nat.beq (mul A Ai) ONE && Nat.beq (mul B Bi) ONE &&
      regC mul ONE A Ai B Bi Ws List.nil fun Rg => k fun u => mwLn mul (letLn A Ai B Bi ONE Rg) u ONE

end CFSG.KC.SporCov

end
