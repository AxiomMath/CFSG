module

public import Certificates.Data.Kernel.Misc.YamakiNA

public section

namespace CFSG.KD.YamakiNA

open CFSG.KD.BfsK CFSG.KD.YamakiA0 CFSG.ClassicalInvolution.Sp62Rec
  CFSG.ClassicalInvolution.Solomon73.Yamaki
open CFSG.KD.Sp62 (MULF ONE)

@[expose] noncomputable def orbN (R : Nat → Nat) (x : List Nat) (cs : List (List Nat)) : List Nat :=
  cs.map fun c => wordN R (conjWord c x)

@[expose] noncomputable def closedN (R : Nat → Nat) (l : List Nat) : Bool :=
  idxN0.all fun s => l.all fun y => l.contains (MULF (MULF (R s) y) (R s))

@[expose] noncomputable def orbK (R RA : Nat → Nat) : Bool :=
  let la := orbN R [5] orbAlphaWords
  let lb := orbN R [4] orbPi12Words
  let lc := orbN R [5, 4] orbPi3Words
  let ld := orbN R [3, 7] orbRhoWords
  decide (la ++ lb ++ lc ++ ld).Nodup && closedN R la && closedN R lb && closedN R lc &&
    closedN R ld && (List.range 64).all fun t =>
      Nat.beq (recX RA 12 t) ONE || (la ++ lb ++ lc ++ ld).contains (recX RA 12 t)

@[expose] noncomputable def e8K (R : Nat → Nat) : Bool :=
  let lb := orbN R [4] orbPi12Words
  !(lb.contains ONE) && lb.all fun y => lb.all fun z => Nat.beq (MULF y z) ONE || lb.contains (MULF y z)

end CFSG.KD.YamakiNA

end
