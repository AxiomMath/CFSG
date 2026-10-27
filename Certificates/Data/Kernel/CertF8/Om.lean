module

public import Certificates.Data.Kernel.CertF8.Pack

public section

namespace CFSG.KC.CertF8.Om

open CFSG.KC.G28 (fld letN letB)
open CFSG.KC.CertF8 (mulS6)

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def impB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true b a

@[expose] noncomputable def notB (a : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false a

@[expose] noncomputable def allFrom (lo cnt : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun d ih => andB ih (f (Nat.add lo d))) cnt

@[expose] def keyM : Nat := 324518553658426726783156020576255

@[expose] noncomputable def keyK (r : Nat) : Nat := Nat.land r keyM

@[expose] def diagM : Nat := 40564838550125678058396201254913

@[expose] noncomputable def canonK (u : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.xor u diagM) u (Nat.beq (Nat.land u 1) 0)

@[expose] noncomputable def stepK (g gi c : Nat) : Nat := canonK (mulS6 (mulS6 g c) gi)

@[expose] noncomputable def rowAt (T G : Nat → Nat) (nG wP lo n : Nat) : Bool :=
  letB (T n) fun r => letB (fld r 108 wP) fun p => letB (fld r (Nat.add 108 wP) 3) fun s =>
    andB (Nat.ble lo p) (andB (Nat.blt p n) (andB (Nat.blt s nG)
      (Nat.beq (keyK r) (stepK (G s) (G (Nat.add s nG)) (keyK (T p))))))

@[expose] noncomputable def sortAt (T S : Nat → Nat) (N i : Nat) : Bool :=
  letB (S i) fun e => letB (keyK e) fun k => letB (fld e 108 17) fun pos =>
    andB (Nat.blt pos N) (andB (Nat.beq (keyK (T pos)) k)
      (impB (Nat.blt (Nat.succ i) N) (Nat.blt k (keyK (S (Nat.succ i))))))

@[expose] def gTab : Nat :=
  70251238829395355573754039211706577597902172474048417563295744459193504377242444184887878130005366725915355528020252802039252639896009540726417091316641477861962128415518991498011101370115280949682723499183110123796570206768184765001622763609344184612865179649

@[expose] noncomputable def gK (s : Nat) : Nat := fld gTab (Nat.mul 108 s) 108

@[expose] def hTab : Nat :=
  2600431206435859042957065437821395142566168422587495378467304977571391616407367765638546054211203727935184180903403149690717950864322903087172950812587495226915219030770150802832385694519418184551519496240348096527809594146326574488169180766799310610773131131897579534706485739603613525543224565917640791939641224967148448278392600927382386373641882670088041828655703554331597411609965927488826087612246251537344997358000810084930786258072082464357193540072858754595046602015475059871519748439608976229125310738750529729

@[expose] noncomputable def hK (t : Nat) : Nat := fld hTab (Nat.mul 108 t) 108

@[expose] noncomputable def symW (w : List Nat) : Nat :=
  w.foldl (fun A s => mulS6 A (gK s)) CFSG.KC.G28.idP

@[expose] noncomputable def symWi (w : List Nat) : Nat :=
  w.reverse.foldl (fun A s => mulS6 A (gK (Nat.mod (Nat.add s 4) 8))) CFSG.KC.G28.idP

@[expose] noncomputable def loK (n : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) 97984 65152 (Nat.blt n 97984)) 32320 (Nat.blt n 65152))
      1 (Nat.blt n 32320)) 0 (Nat.blt n 1)

@[expose] noncomputable def forestAt (T : Nat → Nat) (n : Nat) : Bool :=
  letB (loK n) fun lo => Bool.rec (motive := fun _ => Bool) (rowAt T gK 4 17 lo n) true (Nat.beq n lo)

@[expose] noncomputable def hAt (H : Nat → Nat) (n : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (rowAt H hK 8 10 0 n) true (Nat.beq n 0)

end CFSG.KC.CertF8.Om

end
