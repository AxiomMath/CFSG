module

public import Certificates.Data.Kernel.SporSch.MathieuOC2

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] def bval : List Bool → Nat
  | [] => 1
  | b :: bs => 2 * bval bs + cond b 1 0

@[expose] noncomputable def pbK (n w m p : Nat) (eb : List Bool) : Nat :=
  List.rec (motive := fun _ => Nat) p
    (fun b _ ih => strictN (pcomp n w m ih ih) (fun s => nIf(b, pcomp n w m p s, s))) eb

@[expose] noncomputable def anyWitK (n w m idn : Nat) (eb : List Bool) (ws : List (Nat × Nat))
    (y : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun pr _ ih => Prod.rec (motive := fun _ => Bool)
    (fun c ci => bIf(Nat.beq (pbK n w m (pcomp n w m y (pcomp n w m c (pcomp n w m y ci))) eb) idn,
      ih, true)) pr) ws

@[expose] noncomputable def oddBadK (n w m idn : Nat) (eb : List Bool) (ws : List (Nat × Nat))
    (y : Nat) : Bool :=
  bIf(Nat.beq y idn, false, bIf(Nat.beq (pbK n w m y eb) idn,
    bIf(anyWitK n w m idn eb ws y, false, true), false))

@[expose] noncomputable def allPairsK (f : Nat → Nat → Bool) (ws : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun pr _ ih => Prod.rec (motive := fun _ => Bool) (fun c ci => bAnd(f c ci, ih)) pr) ws

@[expose] noncomputable def cntOddBad2K (n w m nw idn : Nat) (LR TR : Nat → Nat) (nb : Nat)
    (eb : List Bool) (ws : List (Nat × Nat)) (k₀ k₁ : Nat) : Nat :=
  enumFrom n w m nw LR TR (oddBadK n w m idn eb ws) (Nat.sub nb (nat_lit 2)) (nat_lit 2)
    (start2 n w m nw LR TR idn k₀ k₁) (nat_lit 0)

end CFSG.KS.SporSch.MOC

end
