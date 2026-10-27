module

public import Certificates.Data.Kernel.TabMatGrp

public section

namespace CFSG.KC.SporCov

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.F2W

@[expose] noncomputable def letF (MA MAi MB MBi c : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) MBi MB (Nat.beq c (nat_lit 2)))
      MAi (Nat.beq c (nat_lit 1)))
    MA (Nat.beq c (nat_lit 0))

@[expose] noncomputable def mwF (d MA MAi MB MBi : Nat) (w : List Nat) (acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun c _ ih acc => strictN (mulW d (letF MA MAi MB MBi c) acc) ih) w acc

@[expose] noncomputable def eqF (d MA MAi MB MBi : Nat) (u v : List Nat) : Bool :=
  Nat.beq (mwF d MA MAi MB MBi u (idF d)) (mwF d MA MAi MB MBi v (idF d))

@[expose] noncomputable def letL (c : Nat) : Bool := Nat.blt c (nat_lit 4)

@[expose] noncomputable def kitF (d MA MB eA eB : Nat) (k : (List Nat → List Nat → Bool) → Bool) :
    Bool :=
  strictB (powK d MA (Nat.pred eA)) fun MAi => strictB (powK d MB (Nat.pred eB)) fun MBi =>
    andB (Nat.beq (mulF d MA MAi) (idF d)) (andB (Nat.beq (mulF d MB MBi) (idF d))
      (k (eqF d MA MAi MB MBi)))

end CFSG.KC.SporCov

end
