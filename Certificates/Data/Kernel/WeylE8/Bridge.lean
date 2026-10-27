module

public import Certificates.Data.Kernel.WeylE8.Frame

public section

namespace CFSG.KLC.E8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def wordK (RT : Nat → Nat) (W n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn (nat_lit 240) (nat_lit 8))
    (fun k ih => strictN ih fun A =>
      pcomp (nat_lit 240) (nat_lit 8) (nat_lit 255) (RT (e8 W (Nat.sub (Nat.sub n k) (nat_lit 1)))) A) n

@[expose] noncomputable def owK (OWP i : Nat) : Nat := Nat.shiftRight OWP (Nat.mul (nat_lit 32) i)

@[expose] noncomputable def pairK (NEG PAP PRP : Nat) : Bool :=
  bAnd(allN (nat_lit 240) (fun x => strictB (e8 PAP x) fun p =>
      bAnd(Nat.blt p (nat_lit 120), Nat.beq (e8 PAP (e8 NEG x)) p)),
  bAnd(allN (nat_lit 240) (fun x => strictB (e8 PAP x) fun p => strictB (e8 NEG x) fun nx =>
      allN (nat_lit 240) fun y => bIf(Nat.beq (e8 PAP y) p, bIf(Nat.beq y x, true, Nat.beq y nx), true)),
    allN (nat_lit 120) (fun j => strictB (e8 PRP j) fun r =>
      bAnd(Nat.blt r (nat_lit 240), Nat.beq (e8 PAP r) j))))

@[expose] noncomputable def zK (RT : Nat → Nat) (NEG FRP : Nat) : Bool :=
  Nat.beq (wordK RT FRP (nat_lit 8)) (low NEG)

@[expose] noncomputable def omK (RT : Nat → Nat) (PAP PRP OWP : Nat) (GS : Nat → Nat) : Bool :=
  allN (nat_lit 8) fun i => strictB (wordK RT (owK OWP i) (nat_lit 4)) fun X =>
    allN (nat_lit 120) fun j =>
      Nat.beq (e8 PAP (e8 X (e8 PRP j))) (pg (nat_lit 9) (nat_lit 511) (GS i) j)

@[expose] noncomputable def triK (RT : Nat → Nat) (NEG OWP : Nat) : Bool :=
  strictB (wordK RT (owK OWP (nat_lit 0)) (nat_lit 4)) fun W0 =>
  strictB (wordK RT (owK OWP (nat_lit 4)) (nat_lit 4)) fun W4 =>
  strictB (wordK RT (owK OWP (nat_lit 6)) (nat_lit 4)) fun W6 =>
  strictB (pcomp (nat_lit 240) (nat_lit 8) (nat_lit 255) W4 W6) fun U =>
  strictB (pcomp (nat_lit 240) (nat_lit 8) (nat_lit 255) W6 W0) fun Y =>
  strictB (pcomp (nat_lit 240) (nat_lit 8) (nat_lit 255) Y Y) fun Y2 =>
    bAnd(Nat.beq (pcomp (nat_lit 240) (nat_lit 8) (nat_lit 255) U U) (pidn (nat_lit 240) (nat_lit 8)),
      bAnd(notB' (Nat.beq Y2 (pidn (nat_lit 240) (nat_lit 8))), Nat.beq Y2 (low NEG)))

@[expose] noncomputable def pairImg (RT : Nat → Nat) (PAP PRP r : Nat) : Nat :=
  strictN (RT r) fun X => pmk (nat_lit 120) (nat_lit 9) fun j => e8 PAP (e8 X (e8 PRP j))

end CFSG.KLC.E8

end
