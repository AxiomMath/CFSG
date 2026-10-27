module

public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.MonsterConv.PermValid
public import CFSG.Certificates.Kernel.LieCocycle.Fi22.NwValid
public import Certificates.Data.Kernel.YModel.Model

public section

namespace CFSG.KC.Fi24Pair

open CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.MonsterConv.Perm CFSG.KLC.Fi22

@[expose] noncomputable def W24 : Nat := nat_lit 16777216

@[expose] noncomputable def R24 : Nat := Nat.div (maskN W24) M4096

@[expose] noncomputable def trS (t : Nat) : Nat :=
  Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.add t (nat_lit 12))) (Nat.shiftLeft (nat_lit 1) t)

@[expose] noncomputable def trM (t : Nat) : Nat :=
  Nat.land (idPlane W24 t) (Nat.xor (ones W24) (idPlane W24 (Nat.add t (nat_lit 12))))

@[expose] noncomputable def tr (X : Nat) : Nat :=
  iterN (nat_lit 12) (fun t Y => dsw (trS t) (trM t) Y) X

@[expose] noncomputable def preP (NW X : Nat) : Nat :=
  tr (applyNW NW R24 (tr (applyNW NW R24 X)))

@[expose] noncomputable def closedOK (NW M : Nat) : Bool :=
  andB (nwValid NW) (Nat.beq (Nat.lor M (preP NW M)) M)

@[expose] noncomputable def planesNW (NW : Nat) : Nat :=
  netApply (nat_lit 12) (nat_lit 4096) (repU (nat_lit 4096) (nat_lit 12)) NW (idP (nat_lit 12))

@[expose] noncomputable def entP (PL p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b acc => Nat.lor acc (Nat.shiftLeft
      (Nat.land (Nat.shiftRight PL (Nat.add (Nat.mul (nat_lit 4096) b) p)) (nat_lit 1)) b))
    (nat_lit 12)

@[expose] noncomputable def sigOK (LR : Nat → Nat → Nat) (FP : Nat → Nat) (NW r : Nat) : Bool :=
  andB (netValid (nat_lit 12) NW) (letB (planesNW NW) (fun PL =>
    allBelow (nat_lit 3240) (nat_lit 51) (fun p => letB (entP PL p) (fun q =>
      andB (Nat.blt q (nat_lit 3240)) (Nat.beq (LR r (FP p)) (FP q))))))

@[expose] noncomputable def fOK (FP : Nat → Nat) : Bool :=
  allBelow (nat_lit 3240) (nat_lit 51) (fun p => andB (Nat.blt (FP p) (nat_lit 306936))
    (bIf(Nat.blt (Nat.succ p) (nat_lit 3240), Nat.blt (FP p) (FP (Nat.succ p)), true)))

@[expose] noncomputable def region : Nat :=
  Nat.mul (ones (nat_lit 3240)) (Nat.div (ones (nat_lit 13271040)) (ones (nat_lit 4096)))

@[expose] noncomputable def regionOK (M r0 r1 : Nat) : Bool :=
  andB (andB (Nat.blt r0 (nat_lit 3240)) (Nat.blt r1 (nat_lit 3240)))
    (andB (Nat.beq (Nat.land M region) M)
      (Nat.beq (Nat.land (Nat.shiftRight M (Nat.add (Nat.mul (nat_lit 4096) r0) r1)) (nat_lit 1))
        (nat_lit 1)))

@[expose] noncomputable def reachK (k : Nat) (Ns : List Nat) (b R : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (Nat.shiftLeft (nat_lit 1) b)
    (fun _ X => strictN (orbStep k Ns X) (fun Y => Y)) R

@[expose] noncomputable def hOK (Ns : List Nat) (HN r0 : Nat) : Bool :=
  andB (wordNetV (nat_lit 12) Ns HN) (Nat.beq (entP (planesNW HN) r0) r0)

@[expose] noncomputable def absent (FP : Nat → Nat) (u : Nat) : Bool :=
  allBelow (nat_lit 3240) (nat_lit 51) (fun p => notB (Nat.beq (FP p) u))

@[expose] noncomputable def locOK (FP : Nat → Nat) (u iu : Nat) : Bool :=
  bIf(Nat.blt iu (nat_lit 3240), Nat.beq (FP iu) u, andB (Nat.beq iu (nat_lit 3240)) (absent FP u))

@[expose] noncomputable def outOK (FP : Nat → Nat) (M u iu v iv : Nat) : Bool :=
  andB (andB (locOK FP u iu) (locOK FP v iv))
    (bIf(andB (Nat.blt iu (nat_lit 3240)) (Nat.blt iv (nat_lit 3240)),
      Nat.beq (Nat.land (Nat.shiftRight M (Nat.add (Nat.mul (nat_lit 4096) iu) iv)) (nat_lit 1))
        (nat_lit 0),
      true))

end CFSG.KC.Fi24Pair

end
